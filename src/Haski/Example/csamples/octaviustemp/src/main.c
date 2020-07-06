/* main.c - Application main entry point */

/*
 * Copyright (c) 2015-2016 Intel Corporation
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <zephyr/types.h>
#include <stddef.h>
#include <string.h>
#include <errno.h>
#include <sys/printk.h>
#include <sys/byteorder.h>
#include <zephyr.h>

#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/conn.h>
#include <bluetooth/uuid.h>
#include <bluetooth/gatt.h>

#define BT_UUID_DEVICE                             BT_UUID_DECLARE_16(0xffcc)

#define BT_UUID_TEMPERATURE_SENSOR_SERVICE         BT_UUID_DECLARE_16(0xff11)
#define BT_UUID_TEMPERATURE_SENSOR_CHARACTERISTIC  BT_UUID_DECLARE_16(0xff12)

#define BT_UUID_OCTAVIUS_SERVICE                   BT_UUID_DECLARE_16(0xff21)
#define BT_UUID_OCTAVIUS_CHARACTERISTIC            BT_UUID_DECLARE_16(0xff22)

/*********************************/
int temperature;

static void tempoct_ccc_cfg_changed(const struct bt_gatt_attr *attr,
				       u16_t value)
{
	ARG_UNUSED(attr);

	bool notif_enabled = (value == BT_GATT_CCC_NOTIFY);

	printk("Temperature Notifications %s\n", notif_enabled ? "enabled" : "disabled");
}

static ssize_t read_temperature(struct bt_conn* conn, const struct bt_gatt_attr *attr, void *buf, u16_t len, u16_t offset) {
	return bt_gatt_attr_read(conn, attr, buf, len, offset, &temperature, sizeof(temperature));
}

BT_GATT_SERVICE_DEFINE(temp,
	BT_GATT_PRIMARY_SERVICE(BT_UUID_TEMPERATURE_SENSOR_SERVICE),
	BT_GATT_CHARACTERISTIC(BT_UUID_TEMPERATURE_SENSOR_CHARACTERISTIC,
			       BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY, // it can be read from and subscribed to
			       BT_GATT_PERM_READ, read_temperature, NULL,
			       &temperature),
	BT_GATT_CCC(tempoct_ccc_cfg_changed,
		    BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
);

int bt_gatt_get_temperature(void) { return temperature; }

int bt_gatt_set_temperature(int new_temperature) {
    temperature = new_temperature;
    int rc = bt_gatt_notify(NULL, &temp.attrs[1], &new_temperature, sizeof(new_temperature));
    return rc == -ENOTCONN ? 0 : rc;
}

static void temperature_notify(void)
{
	int current = bt_gatt_get_temperature();
	current -= 1;

	if (!current) {
		current = 35;
	}

	bt_gatt_set_temperature(current);
}

/********** Octavius sensor **********/
int octavius;

static void tempoct2_ccc_cfg_changed(const struct bt_gatt_attr *attr,
				       u16_t value)
{
	ARG_UNUSED(attr);

	bool notif_enabled = (value == BT_GATT_CCC_NOTIFY);

	printk("Octavius Notifications %s\n", notif_enabled ? "enabled" : "disabled");
}

static ssize_t read_octavius(struct bt_conn* conn, const struct bt_gatt_attr *attr, void *buf, u16_t len, u16_t offset) {
	return bt_gatt_attr_read(conn, attr, buf, len, offset, &octavius, sizeof(octavius));
}

BT_GATT_SERVICE_DEFINE(oct,
	BT_GATT_PRIMARY_SERVICE(BT_UUID_OCTAVIUS_SERVICE),
	BT_GATT_CHARACTERISTIC(BT_UUID_OCTAVIUS_CHARACTERISTIC,
			       BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY, // it can be read from and subscribed to
			       BT_GATT_PERM_READ, read_octavius, NULL,
			       &octavius),
	BT_GATT_CCC(tempoct2_ccc_cfg_changed,
		    BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
);

int bt_gatt_get_octavius(void) { return octavius; }

int bt_gatt_set_octavius(int new_octavius) {
    octavius = new_octavius;
    int rc = bt_gatt_notify(NULL, &oct.attrs[1], &new_octavius, sizeof(new_octavius));
    return rc == -ENOTCONN ? 0 : rc;
}

static void octavius_notify(void)
{
	int current = bt_gatt_get_octavius();

	if (!current) {
            current = 1;
	} else {
            current = 0;
        }

	bt_gatt_set_octavius(current);
}
/*************************************/

struct bt_conn *default_conn;

static const struct bt_data ad[] = {
	BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
	// 0xcc & 0xff here is the device UUID defined at the top
	BT_DATA_BYTES(BT_DATA_UUID16_ALL, 0xcc, 0xff, 0xaa, 0xff, 0x0a, 0x18),
};

static void connected(struct bt_conn *conn, u8_t err)
{
	if (err) {
		printk("Connection failed (err 0x%02x)\n", err);
	} else {
		default_conn = bt_conn_ref(conn);
		printk("Connected\n");
	}
}

static void disconnected(struct bt_conn *conn, u8_t reason)
{
	printk("Disconnected (reason 0x%02x)\n", reason);

	if (default_conn) {
		bt_conn_unref(default_conn);
		default_conn = NULL;
	}
}

static struct bt_conn_cb conn_callbacks = {
	.connected = connected,
	.disconnected = disconnected,
};

static void bt_ready(void)
{
	int err;

	printk("Bluetooth initialized\n");

	err = bt_le_adv_start(BT_LE_ADV_CONN_NAME, ad, ARRAY_SIZE(ad), NULL, 0);
	if (err) {
		printk("Advertising failed to start (err %d)\n", err);
		return;
	}

	printk("Advertising successfully started\n");
}

static void auth_cancel(struct bt_conn *conn)
{
	char addr[BT_ADDR_LE_STR_LEN];

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

	printk("Pairing cancelled: %s\n", addr);
}

static struct bt_conn_auth_cb auth_cb_display = {
	.cancel = auth_cancel,
};

void main(void)
{
	temperature = 35;
	octavius = 1;
	int err;

	err = bt_enable(NULL);
	if (err) {
		printk("Bluetooth init failed (err %d)\n", err);
		return;
	}

	bt_ready();

	bt_conn_cb_register(&conn_callbacks);
	bt_conn_auth_cb_register(&auth_cb_display);

	/* Implement notification. At the moment there is no suitable way
	 * of starting delayed work so we do it here
	 */
	while (1) {
		k_sleep(K_SECONDS(1));
                temperature_notify();

		k_sleep(K_SECONDS(1));
		octavius_notify();
	}
}
