/* main.c - Application main entry point */

/*
 * Copyright (c) 2015-2016 Intel Corporation
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <zephyr/types.h>
#include <stddef.h>
#include <errno.h>
#include <zephyr.h>
#include <sys/printk.h>

#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/conn.h>
#include <bluetooth/uuid.h>
#include <bluetooth/gatt.h>
#include <sys/byteorder.h>

#define BT_UUID_DEVICE                             BT_UUID_DECLARE_16(0xffcc)

#define BT_UUID_TEMPERATURE_SENSOR_SERVICE         BT_UUID_DECLARE_16(0xff11)
#define BT_UUID_TEMPERATURE_SENSOR_CHARACTERISTIC  BT_UUID_DECLARE_16(0xff12)

#define BT_UUID_OCTAVIUS_SERVICE                   BT_UUID_DECLARE_16(0xff21)
#define BT_UUID_OCTAVIUS_CHARACTERISTIC            BT_UUID_DECLARE_16(0xff22)

/* This is the generated Halexa code from DSLustre, just
 * pasted in for simplicity. */
/*****************************************************/
struct main_mem
{ int d;
  int c;
};
void (main_reset(struct main_mem (* self))) {
  ((*(self)).d) = (1);
  ((*(self)).c) = (0);
}
int (main_step(struct main_mem (* self))) {
  int b;
  int a;
  (b) = ((*(self)).d);
  (a) = ((*(self)).c);
  ((*(self)).d) = ((a) + (b));
  ((*(self)).c) = (b);
  return a;
}

struct main_mem *obj_main;
int func(int temp, int door) {
    int x = main_step(obj_main);
    printk("%d\n",x);
    return 0;
}
/*****************************************************/

static struct bt_conn *default_conn;

/* These two UUIDs are used for scanning for the two different services */
static struct bt_uuid_16 uuid = BT_UUID_INIT_16(0);
static struct bt_uuid_16 oct_uuid = BT_UUID_INIT_16(0);

/* These fields are used to configure the service/characteristic discovery,
 * one a connection to the remote server has been established. */
static struct bt_gatt_discover_params discover_params;
static struct bt_gatt_discover_params discover_oct_params;
static struct bt_gatt_subscribe_params subscribe_params;
static struct bt_gatt_subscribe_params subscribe_oct_params;

static u8_t notify_temperature(struct bt_conn *conn,
                               struct bt_gatt_subscribe_params *params,
                               const void *data, u16_t length) {
    if (!data) {
        printk("[UNSUBSCRIBED]\n");
        params->value_handle = 0U;
        return BT_GATT_ITER_STOP;
    }

	int* input = (int*) data;

	printk("[NOTIFICATION] data %p length %u\n", data, length);
	printk("[VALUE] temperature %d\n", *input);

	/***** Prepare to call Nachi's function *****/
	/* 0 for door indicates N/A */
	func(*input, 0);
	/********************************************/

	return BT_GATT_ITER_CONTINUE;
}

static u8_t notify_octavius(struct bt_conn *conn,
                            struct bt_gatt_subscribe_params *params,
                            const void *data, u16_t length) {
	if (!data) {
		printk("[UNSUBSCRIBED]\n");
		params->value_handle = 0U;
		return BT_GATT_ITER_STOP;
	}

	int* input = (int*) data;

	printk("[NOTIFICATION] data %p length %u\n", data, length);
	printk("[VALUE] octavius %d\n", *input);

	/***** Prepare to call Nachi's function *****/
	/* -273 indicates N/A */
	func(-273, (*input) + 1);
	/********************************************/

	return BT_GATT_ITER_CONTINUE;
}

static u8_t discover_temperature(struct bt_conn *conn,
                                 const struct bt_gatt_attr *attr,
                                 struct bt_gatt_discover_params *params) {
	int err;

	if (!attr) {
		printk("Discover complete\n");
		(void)memset(params, 0, sizeof(*params));
		return BT_GATT_ITER_STOP;
	}

	printk("[ATTRIBUTE] handle %u\n", attr->handle);

	char uuidstr[64];
	bt_uuid_to_str(attr->uuid, uuidstr, 64);
	printk("found uuid was %s\n", uuidstr);

	if (!bt_uuid_cmp(discover_params.uuid, BT_UUID_TEMPERATURE_SENSOR_SERVICE)) {
		memcpy(&uuid, BT_UUID_TEMPERATURE_SENSOR_CHARACTERISTIC, sizeof(uuid));
		discover_params.uuid = &uuid.uuid;
		discover_params.start_handle = attr->handle + 1;
		discover_params.type = BT_GATT_DISCOVER_CHARACTERISTIC;

		err = bt_gatt_discover(conn, &discover_params);
		if (err) {
			printk("Discover failed (err %d)\n", err);
		}
	} else if (!bt_uuid_cmp(discover_params.uuid, BT_UUID_TEMPERATURE_SENSOR_CHARACTERISTIC)) {
		memcpy(&uuid, BT_UUID_GATT_CCC, sizeof(uuid));
		discover_params.uuid = &uuid.uuid;
		discover_params.start_handle = attr->handle + 2;
		discover_params.type = BT_GATT_DISCOVER_DESCRIPTOR;
		subscribe_params.value_handle = bt_gatt_attr_value_handle(attr);

		err = bt_gatt_discover(conn, &discover_params);
		if (err) {
			printk("Discover failed (err %d)\n", err);
		}
	} else {
		subscribe_params.notify = notify_temperature;
		subscribe_params.value = BT_GATT_CCC_NOTIFY;
		subscribe_params.ccc_handle = attr->handle;

		err = bt_gatt_subscribe(conn, &subscribe_params);
		if (err && err != -EALREADY) {
			printk("Subscribe failed (err %d)\n", err);
		} else {
			printk("[SUBSCRIBED]\n");
		}

		return BT_GATT_ITER_STOP;
	}

	return BT_GATT_ITER_STOP;
}

static u8_t discover_octavius(struct bt_conn *conn,
			     const struct bt_gatt_attr *attr,
			     struct bt_gatt_discover_params *params)
{
	int err;

	if (!attr) {
		printk("Discover complete\n");
		(void)memset(params, 0, sizeof(*params));
		return BT_GATT_ITER_STOP;
	}

	printk("[ATTRIBUTE] handle %u\n", attr->handle);

	if (!bt_uuid_cmp(discover_oct_params.uuid, BT_UUID_OCTAVIUS_SERVICE)) {
		memcpy(&oct_uuid, BT_UUID_OCTAVIUS_CHARACTERISTIC, sizeof(uuid));
		discover_oct_params.uuid = &oct_uuid.uuid;
		discover_oct_params.start_handle = attr->handle + 1;
		discover_oct_params.type = BT_GATT_DISCOVER_CHARACTERISTIC;

		err = bt_gatt_discover(conn, &discover_oct_params);
		if (err) {
			printk("Discover failed (err %d)\n", err);
		}
	} else if (!bt_uuid_cmp(discover_oct_params.uuid, BT_UUID_OCTAVIUS_CHARACTERISTIC)) {
		memcpy(&oct_uuid, BT_UUID_GATT_CCC, sizeof(uuid));
		discover_oct_params.uuid = &oct_uuid.uuid;
		discover_oct_params.start_handle = attr->handle + 2;
		discover_oct_params.type = BT_GATT_DISCOVER_DESCRIPTOR;
		subscribe_oct_params.value_handle = bt_gatt_attr_value_handle(attr);

		err = bt_gatt_discover(conn, &discover_oct_params);
		if (err) {
			printk("Discover failed (err %d)\n", err);
		}
	} else {
		subscribe_oct_params.notify = notify_octavius;
		subscribe_oct_params.value = BT_GATT_CCC_NOTIFY;
		subscribe_oct_params.ccc_handle = attr->handle;

		err = bt_gatt_subscribe(conn, &subscribe_oct_params);
		if (err && err != -EALREADY) {
			printk("Subscribe failed (err %d)\n", err);
		} else {
			printk("[SUBSCRIBED]\n");
		}

		return BT_GATT_ITER_STOP;
	}

	return BT_GATT_ITER_STOP;
}

static bool eir_found(struct bt_data *data, void *user_data)
{
	bt_addr_le_t *addr = user_data;
	int i;

	printk("[AD]: %u data_len %u\n", data->type, data->data_len);

	switch (data->type) {
	case BT_DATA_UUID16_SOME:
	case BT_DATA_UUID16_ALL:
		if (data->data_len % sizeof(u16_t) != 0U) {
			printk("AD malformed\n");
			return true;
		}

		for (i = 0; i < data->data_len; i += sizeof(u16_t)) {
			struct bt_le_conn_param *param;
			struct bt_uuid *uuid;
			u16_t u16;
			int err;

			memcpy(&u16, &data->data[i], sizeof(u16));
			uuid = BT_UUID_DECLARE_16(sys_le16_to_cpu(u16));
			if (bt_uuid_cmp(uuid, BT_UUID_DEVICE)) {
				continue;
			}

			err = bt_le_scan_stop();
			if (err) {
				printk("Stop LE scan failed (err %d)\n", err);
				continue;
			}

			param = BT_LE_CONN_PARAM_DEFAULT;
			err = bt_conn_le_create(addr, BT_CONN_LE_CREATE_CONN,
						param, &default_conn);
			if (err) {
				printk("Create conn failed (err %d)\n", err);
			}

			return false;
		}
	}

	return true;
}

static void device_found(const bt_addr_le_t *addr, s8_t rssi, u8_t type,
			 struct net_buf_simple *ad)
{
	char dev[BT_ADDR_LE_STR_LEN];

	bt_addr_le_to_str(addr, dev, sizeof(dev));
	printk("[DEVICE]: %s, AD evt type %u, AD data len %u, RSSI %i\n",
	       dev, type, ad->len, rssi);

	/* We're only interested in connectable events */
	if (type == BT_GAP_ADV_TYPE_ADV_IND ||
	    type == BT_GAP_ADV_TYPE_ADV_DIRECT_IND) {
		bt_data_parse(ad, eir_found, (void *)addr);
	}
}

static void start_scan(void)
{
	int err;

	/* Use active scanning and disable duplicate filtering to handle any
	 * devices that might update their advertising data at runtime. */
	struct bt_le_scan_param scan_param = {
		.type       = BT_LE_SCAN_TYPE_ACTIVE,
		.options    = BT_LE_SCAN_OPT_NONE,
		.interval   = BT_GAP_SCAN_FAST_INTERVAL,
		.window     = BT_GAP_SCAN_FAST_WINDOW,
	};

	err = bt_le_scan_start(&scan_param, device_found);
	if (err) {
		printk("Scanning failed to start (err %d)\n", err);
		return;
	}

	printk("Scanning successfully started\n");
}

static void connected(struct bt_conn *conn, u8_t conn_err)
{
	char addr[BT_ADDR_LE_STR_LEN];
	int err;

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

	if (conn_err) {
		printk("Failed to connect to %s (%u)\n", addr, conn_err);

		bt_conn_unref(default_conn);
		default_conn = NULL;

		start_scan();
		return;
	}

	printk("Connected: %s\n", addr);

	if (conn == default_conn) {
		printk("Initiating scan for the octavius service\n");
		memcpy(&oct_uuid, BT_UUID_OCTAVIUS_SERVICE, sizeof(uuid));
		discover_oct_params.uuid = &oct_uuid.uuid;
		discover_oct_params.func = discover_octavius;
		discover_oct_params.start_handle = 0x0001;
		discover_oct_params.end_handle = 0xffff;
		discover_oct_params.type = BT_GATT_DISCOVER_PRIMARY;

		err = bt_gatt_discover(default_conn, &discover_oct_params);
		if (err) {
			printk("Discover failed(err %d)\n", err);
			return;
		}

		printk("Initiating scan for the temperature service\n");
		memcpy(&uuid, BT_UUID_TEMPERATURE_SENSOR_SERVICE, sizeof(uuid));
		discover_params.uuid = &uuid.uuid;
		discover_params.func = discover_temperature;
		discover_params.start_handle = 0x0001;
		discover_params.end_handle = 0xffff;
		discover_params.type = BT_GATT_DISCOVER_PRIMARY;

		err = bt_gatt_discover(default_conn, &discover_params);
		if (err) {
			printk("Discover failed(err %d)\n", err);
			return;
		}
		
	}
}

static void disconnected(struct bt_conn *conn, u8_t reason)
{
	char addr[BT_ADDR_LE_STR_LEN];

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

	printk("Disconnected: %s (reason 0x%02x)\n", addr, reason);

	if (default_conn != conn) {
		return;
	}

	bt_conn_unref(default_conn);
	default_conn = NULL;

	start_scan();
}

static struct bt_conn_cb conn_callbacks = {
	.connected = connected,
	.disconnected = disconnected,
};

void start_bt(void)
{
	int err;
	err = bt_enable(NULL);

	if (err) {
		printk("Bluetooth init failed (err %d)\n", err);
		return;
	}

	printk("Bluetooth initialized\n");

	bt_conn_cb_register(&conn_callbacks);

	start_scan();
}

void main(void) {
    obj_main = k_malloc (sizeof(struct main_mem));
    main_reset(obj_main);
    start_bt();
}
