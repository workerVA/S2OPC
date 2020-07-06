/*
 * Licensed to Systerel under one or more contributor license
 * agreements. See the NOTICE file distributed with this work
 * for additional information regarding copyright ownership.
 * Systerel licenses this file to you under the Apache
 * License, Version 2.0 (the "License"); you may not use this
 * file except in compliance with the License. You may obtain
 * a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#ifndef TESTS_DATA_CERT_STATIC_SECURITY_DATA_H_
#define TESTS_DATA_CERT_STATIC_SECURITY_DATA_H_

/* Note: following command might be used to extract the certificate content:
 * hexdump -v -e '/1 "0x%02X,"'
 */

static const unsigned char cacert[] = {
    0x30, 0x82, 0x06, 0x0d, 0x30, 0x82, 0x03, 0xf5, 0xa0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x09, 0x00, 0xa0, 0xb7, 0x0a,
    0x15, 0xc7, 0xb7, 0x71, 0x14, 0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05,
    0x00, 0x30, 0x81, 0x93, 0x31, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x46, 0x52, 0x31, 0x0f,
    0x30, 0x0d, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0c, 0x06, 0x46, 0x72, 0x61, 0x6e, 0x63, 0x65, 0x31, 0x11, 0x30, 0x0f,
    0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c, 0x08, 0x53, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x31, 0x36, 0x30, 0x34,
    0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x2d, 0x53, 0x32, 0x4f, 0x50, 0x43, 0x20, 0x43, 0x65, 0x6e, 0x74, 0x75, 0x72,
    0x79, 0x20, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x20, 0x41, 0x75, 0x74, 0x68, 0x6f,
    0x72, 0x69, 0x74, 0x79, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x54, 0x65, 0x73, 0x74, 0x73, 0x31, 0x28, 0x30, 0x26, 0x06,
    0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x01, 0x16, 0x19, 0x73, 0x32, 0x6f, 0x70, 0x63, 0x2d, 0x73,
    0x75, 0x70, 0x70, 0x6f, 0x72, 0x74, 0x40, 0x73, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x2e, 0x66, 0x72, 0x30,
    0x20, 0x17, 0x0d, 0x31, 0x38, 0x31, 0x30, 0x30, 0x34, 0x31, 0x35, 0x34, 0x37, 0x35, 0x37, 0x5a, 0x18, 0x0f, 0x32,
    0x31, 0x31, 0x38, 0x30, 0x39, 0x31, 0x30, 0x31, 0x35, 0x34, 0x37, 0x35, 0x37, 0x5a, 0x30, 0x81, 0x93, 0x31, 0x0b,
    0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x46, 0x52, 0x31, 0x0f, 0x30, 0x0d, 0x06, 0x03, 0x55, 0x04,
    0x08, 0x0c, 0x06, 0x46, 0x72, 0x61, 0x6e, 0x63, 0x65, 0x31, 0x11, 0x30, 0x0f, 0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c,
    0x08, 0x53, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x31, 0x36, 0x30, 0x34, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c,
    0x2d, 0x53, 0x32, 0x4f, 0x50, 0x43, 0x20, 0x43, 0x65, 0x6e, 0x74, 0x75, 0x72, 0x79, 0x20, 0x43, 0x65, 0x72, 0x74,
    0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x20, 0x41, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x74, 0x79, 0x20, 0x66,
    0x6f, 0x72, 0x20, 0x54, 0x65, 0x73, 0x74, 0x73, 0x31, 0x28, 0x30, 0x26, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7,
    0x0d, 0x01, 0x09, 0x01, 0x16, 0x19, 0x73, 0x32, 0x6f, 0x70, 0x63, 0x2d, 0x73, 0x75, 0x70, 0x70, 0x6f, 0x72, 0x74,
    0x40, 0x73, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x2e, 0x66, 0x72, 0x30, 0x82, 0x02, 0x22, 0x30, 0x0d, 0x06,
    0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x82, 0x02, 0x0f, 0x00, 0x30, 0x82,
    0x02, 0x0a, 0x02, 0x82, 0x02, 0x01, 0x00, 0xcf, 0xd7, 0xb7, 0xf1, 0x35, 0x62, 0xf1, 0xc1, 0x63, 0xe6, 0x05, 0x5b,
    0xc4, 0x58, 0xc6, 0xed, 0x53, 0x67, 0x5f, 0xeb, 0x7b, 0x7c, 0xa0, 0xe8, 0x68, 0x8d, 0x4c, 0x3a, 0xd6, 0x03, 0xa5,
    0xfe, 0x5d, 0x85, 0x4d, 0x16, 0x67, 0x69, 0x1f, 0x9e, 0x8e, 0x35, 0x03, 0xbe, 0xa1, 0xbe, 0xdc, 0xcf, 0xb6, 0xfc,
    0x58, 0x14, 0x2b, 0xd5, 0x5a, 0x37, 0x9a, 0x4c, 0x01, 0x07, 0x82, 0xdf, 0x96, 0xfb, 0x45, 0x5e, 0x46, 0x7a, 0xa7,
    0x85, 0xae, 0xc3, 0xf9, 0xd2, 0x0f, 0x86, 0x34, 0x04, 0x77, 0xc1, 0x83, 0x23, 0x55, 0x33, 0xf8, 0xd4, 0x52, 0x2e,
    0x12, 0xe0, 0xcb, 0xcb, 0xf4, 0xe6, 0x1c, 0xc8, 0xf8, 0x0f, 0x62, 0x66, 0x31, 0x1c, 0x86, 0x47, 0x02, 0x0a, 0x9e,
    0xb3, 0x39, 0xde, 0xbb, 0x2e, 0x9c, 0x88, 0x87, 0xa8, 0x41, 0xb4, 0xa1, 0x72, 0xcf, 0xaf, 0x20, 0x84, 0xfd, 0xea,
    0xa4, 0xd5, 0xd7, 0xd3, 0x3f, 0x71, 0x1b, 0x4f, 0x2e, 0xee, 0x44, 0x1a, 0x54, 0x9b, 0x62, 0xda, 0xd6, 0xbd, 0x66,
    0x31, 0x22, 0x16, 0x77, 0xde, 0xde, 0x02, 0x7c, 0x85, 0xb3, 0x9f, 0xdd, 0x64, 0x61, 0xb7, 0xe5, 0x69, 0x6a, 0x2f,
    0x8c, 0x1d, 0x22, 0x73, 0xde, 0x1e, 0x4d, 0x79, 0x6c, 0xad, 0xe3, 0x86, 0x00, 0x8d, 0x41, 0xa6, 0xee, 0x2f, 0x54,
    0x0d, 0x48, 0x23, 0x27, 0x7c, 0x04, 0x9e, 0x9c, 0x8f, 0x3c, 0xcf, 0xb7, 0xf3, 0x5d, 0x89, 0x53, 0xd8, 0x62, 0xc1,
    0x0e, 0x29, 0xff, 0xcb, 0xb7, 0x27, 0xab, 0xe4, 0xb3, 0x77, 0x35, 0xad, 0x06, 0x9f, 0xa2, 0xcf, 0xa2, 0xe9, 0xc7,
    0x34, 0x4e, 0x0a, 0x3a, 0x02, 0x02, 0xfc, 0xcb, 0x4a, 0x87, 0x98, 0xbb, 0x7e, 0x7c, 0x66, 0x68, 0xbc, 0x67, 0x8c,
    0x29, 0xea, 0x53, 0x87, 0xbe, 0x97, 0x38, 0x67, 0x42, 0x28, 0x29, 0x4b, 0x99, 0x63, 0x5c, 0x57, 0xbb, 0x37, 0x6a,
    0x10, 0x1d, 0x83, 0xa6, 0x55, 0xde, 0xf9, 0xb2, 0x98, 0xab, 0x56, 0xbb, 0xee, 0x95, 0xbe, 0x80, 0xd5, 0x3e, 0x9c,
    0x2e, 0xef, 0xfa, 0xf4, 0x4f, 0x1f, 0xc3, 0x1a, 0xd6, 0xaa, 0x1d, 0x3d, 0xa5, 0x9b, 0x15, 0x4e, 0xea, 0x7e, 0x09,
    0xbb, 0xdb, 0x89, 0x74, 0x14, 0x09, 0x7b, 0x15, 0xd0, 0xcf, 0xe3, 0x5a, 0x7b, 0xc8, 0x5a, 0xd8, 0x5b, 0x4c, 0x43,
    0xd8, 0xb7, 0x4b, 0xef, 0xc4, 0xdf, 0xff, 0xf3, 0x73, 0x1e, 0x45, 0x90, 0x35, 0xb5, 0xd7, 0x5b, 0x28, 0x89, 0x60,
    0xa7, 0xbe, 0x2f, 0x7c, 0xae, 0xda, 0xd2, 0xfb, 0x7f, 0x42, 0x7d, 0x9f, 0x92, 0x3b, 0xc6, 0xe9, 0xbb, 0x0d, 0x6d,
    0xde, 0x17, 0xe4, 0x08, 0xe0, 0x24, 0xc3, 0xeb, 0x44, 0xb0, 0xd0, 0x06, 0xc3, 0x7c, 0xd5, 0xb3, 0x35, 0x3d, 0x85,
    0x79, 0xac, 0xc3, 0xe7, 0xc0, 0x75, 0xde, 0x71, 0x2a, 0xe6, 0xae, 0x81, 0x9e, 0x05, 0x40, 0x12, 0x87, 0x1f, 0x43,
    0xff, 0x30, 0x64, 0xac, 0x06, 0x53, 0x8c, 0x17, 0xac, 0x1e, 0x76, 0x44, 0xf3, 0x85, 0x8d, 0x62, 0x31, 0x80, 0x39,
    0xe4, 0x9c, 0xf5, 0x66, 0xb4, 0x0f, 0xe3, 0xd4, 0xe8, 0x98, 0x1f, 0xde, 0xac, 0xef, 0x03, 0x9e, 0x67, 0x26, 0x31,
    0x2f, 0x86, 0x12, 0xd8, 0x8d, 0xa1, 0x45, 0xfd, 0xf5, 0x5d, 0x99, 0xf5, 0xb3, 0x36, 0xbc, 0xa6, 0x73, 0x93, 0x8e,
    0x42, 0x6b, 0xf2, 0x56, 0x38, 0x54, 0x0c, 0x2e, 0x80, 0xc7, 0xaf, 0x5b, 0x85, 0x22, 0xc3, 0x07, 0x95, 0xc7, 0x4b,
    0x14, 0xaf, 0x10, 0x59, 0xc6, 0x2a, 0xcb, 0x0f, 0xa7, 0x9e, 0x56, 0x3c, 0xc9, 0x07, 0xa9, 0x97, 0x15, 0x56, 0x54,
    0x94, 0x2c, 0xdf, 0x9d, 0xaf, 0xac, 0x4f, 0xc9, 0xc1, 0x4f, 0x66, 0x83, 0x8e, 0xb7, 0x66, 0x53, 0x9d, 0x98, 0x43,
    0xeb, 0xb5, 0xf9, 0x35, 0x06, 0x45, 0x02, 0x03, 0x01, 0x00, 0x01, 0xa3, 0x60, 0x30, 0x5e, 0x30, 0x1d, 0x06, 0x03,
    0x55, 0x1d, 0x0e, 0x04, 0x16, 0x04, 0x14, 0x7a, 0x46, 0xcb, 0xd2, 0x2f, 0x30, 0xa4, 0xff, 0x67, 0x29, 0x13, 0x39,
    0x3f, 0x9c, 0x02, 0xbf, 0x03, 0xd0, 0x72, 0x82, 0x30, 0x1f, 0x06, 0x03, 0x55, 0x1d, 0x23, 0x04, 0x18, 0x30, 0x16,
    0x80, 0x14, 0x7a, 0x46, 0xcb, 0xd2, 0x2f, 0x30, 0xa4, 0xff, 0x67, 0x29, 0x13, 0x39, 0x3f, 0x9c, 0x02, 0xbf, 0x03,
    0xd0, 0x72, 0x82, 0x30, 0x0f, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x01, 0x01, 0xff, 0x04, 0x05, 0x30, 0x03, 0x01, 0x01,
    0xff, 0x30, 0x0b, 0x06, 0x03, 0x55, 0x1d, 0x0f, 0x04, 0x04, 0x03, 0x02, 0x01, 0x06, 0x30, 0x0d, 0x06, 0x09, 0x2a,
    0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x03, 0x82, 0x02, 0x01, 0x00, 0x1f, 0xbc, 0x52, 0x5a,
    0x49, 0x6d, 0x0f, 0xab, 0x7a, 0x62, 0xe6, 0x07, 0x4d, 0xd9, 0x94, 0xc8, 0xc9, 0xbd, 0xee, 0xb1, 0x1a, 0x34, 0xaa,
    0x9f, 0x32, 0x03, 0xc5, 0x36, 0x04, 0x82, 0x69, 0x91, 0xca, 0x1d, 0x02, 0xa3, 0x1c, 0x28, 0xf9, 0xad, 0xd8, 0xdd,
    0xdf, 0x63, 0x68, 0x11, 0x80, 0x90, 0x2b, 0xc5, 0xa0, 0x4a, 0x22, 0x56, 0xc4, 0xea, 0x28, 0xd4, 0x4e, 0x23, 0x43,
    0xb5, 0x3a, 0xf6, 0x95, 0x1d, 0xb2, 0xdc, 0xe9, 0xbf, 0xfa, 0xee, 0x59, 0x6e, 0x3f, 0xc2, 0x1f, 0x0b, 0x02, 0x58,
    0xf7, 0x7f, 0x0a, 0xf3, 0xfe, 0xf4, 0xe1, 0xbc, 0x0d, 0x88, 0x62, 0xd6, 0x7c, 0x8e, 0x5c, 0x23, 0x01, 0x46, 0xbe,
    0x59, 0x39, 0x13, 0xbc, 0x3a, 0xd9, 0x68, 0x07, 0x89, 0x64, 0x72, 0xf5, 0x21, 0xe4, 0xad, 0xb7, 0x4b, 0x0a, 0xf3,
    0xef, 0xea, 0xdb, 0x48, 0xa1, 0x73, 0xa1, 0x0f, 0xcc, 0x67, 0x57, 0x7e, 0x0d, 0xff, 0x2f, 0xee, 0xf3, 0x55, 0x6e,
    0x36, 0x68, 0x9d, 0xbf, 0xf5, 0x89, 0x1b, 0x95, 0x50, 0x6e, 0xa0, 0x0d, 0x2b, 0x26, 0x5a, 0x48, 0x88, 0x95, 0xa3,
    0xf6, 0x6b, 0xf4, 0xb6, 0x23, 0x46, 0x6c, 0x2f, 0x58, 0x31, 0xc6, 0xa5, 0x8e, 0xe4, 0x55, 0x93, 0x6a, 0x62, 0x0d,
    0xb9, 0xf8, 0x19, 0x87, 0x0a, 0x23, 0xee, 0x21, 0x3d, 0xb1, 0x9c, 0x2f, 0xff, 0x3c, 0xa0, 0xc2, 0x62, 0xf2, 0x29,
    0x28, 0xd1, 0xf8, 0xc6, 0x2e, 0x8c, 0x4a, 0xec, 0x5e, 0x3a, 0xcd, 0xc7, 0x50, 0xe5, 0xd4, 0x4c, 0x8c, 0x3b, 0x43,
    0xf8, 0x5a, 0x67, 0x81, 0xb8, 0xae, 0x37, 0x37, 0x81, 0xf7, 0x29, 0x55, 0x38, 0x9f, 0x06, 0x6e, 0x5a, 0xca, 0x00,
    0x9f, 0xec, 0xe8, 0xbd, 0x87, 0x33, 0xac, 0x2e, 0xd1, 0x25, 0x0b, 0x99, 0xc6, 0xa9, 0x5c, 0x4c, 0x0b, 0x0c, 0xf5,
    0x46, 0xcc, 0x55, 0xc6, 0x46, 0x7f, 0x13, 0x70, 0x9e, 0x53, 0x13, 0xea, 0x64, 0x87, 0x2c, 0x8a, 0xe3, 0x85, 0xe3,
    0x21, 0xd3, 0x53, 0x0c, 0x21, 0x41, 0x2e, 0x06, 0x1f, 0x8c, 0x22, 0xb6, 0x69, 0x6f, 0xc8, 0x04, 0x19, 0xbc, 0x59,
    0x01, 0xb7, 0x42, 0x4e, 0x28, 0xfc, 0xa6, 0x72, 0x1f, 0x57, 0xc9, 0x8c, 0xfa, 0x26, 0x48, 0x6e, 0x09, 0x37, 0x76,
    0x4a, 0x1a, 0xb9, 0x0b, 0xe7, 0xd5, 0x9c, 0x7b, 0xa0, 0x6e, 0xb3, 0xcb, 0xa0, 0x8d, 0x64, 0x01, 0x63, 0xa0, 0x46,
    0xf2, 0xa3, 0xaa, 0xf2, 0x3f, 0xd7, 0x83, 0xd0, 0x56, 0xaf, 0x1c, 0xae, 0x59, 0x0f, 0xff, 0x8e, 0x14, 0x91, 0xee,
    0xfc, 0xa9, 0x5c, 0x12, 0xf3, 0x94, 0x3b, 0x8c, 0x38, 0x76, 0xcd, 0xf1, 0x8f, 0xcd, 0x31, 0xf0, 0x3a, 0x9a, 0x05,
    0x53, 0x48, 0xe2, 0x05, 0x14, 0x39, 0x7b, 0xef, 0xf7, 0xe2, 0x36, 0xaa, 0x1b, 0x86, 0x90, 0x35, 0xb8, 0x61, 0x07,
    0x2a, 0xa5, 0xba, 0xc4, 0x9a, 0xf4, 0x1e, 0x4f, 0xac, 0x8e, 0xd8, 0xa8, 0x76, 0xfc, 0xbe, 0xb4, 0xb0, 0x2a, 0xb2,
    0x56, 0xd9, 0x02, 0x72, 0x41, 0xd7, 0xd2, 0xb6, 0x16, 0x7e, 0x68, 0x6a, 0x32, 0x8b, 0xdc, 0x5b, 0x16, 0x90, 0x1b,
    0xf4, 0x8a, 0x0d, 0x14, 0x48, 0xd9, 0xa9, 0x59, 0xa8, 0xdf, 0x34, 0xf0, 0x53, 0x82, 0xd1, 0xa0, 0x05, 0x02, 0xa1,
    0x86, 0x67, 0xa1, 0x64, 0x56, 0xa0, 0xc8, 0x45, 0xc5, 0x43, 0xe8, 0x99, 0xb7, 0x89, 0x59, 0x55, 0x9a, 0x6c, 0x55,
    0x43, 0xf7, 0x06, 0x7d, 0xce, 0xbb, 0x88, 0xc1, 0x4f, 0x64, 0x69, 0x87, 0x50, 0x48, 0x8a, 0x3f, 0xb6, 0x0a, 0x21,
    0x63, 0xd7, 0xd5, 0x04, 0xaa, 0x47, 0x0e, 0x9c, 0x96, 0xc6, 0x9c, 0x9f, 0xc5, 0xcc, 0xd8, 0x44, 0x84, 0x12, 0x27,
    0x43, 0xc2, 0xc2, 0xe5, 0xd4, 0xdf, 0x6a, 0xf8, 0xde, 0x89, 0x52, 0x56, 0x1e, 0xb6};

static const unsigned char cacrl[] = {
    0x30, 0x82, 0x02, 0xdc, 0x30, 0x81, 0xc5, 0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01,
    0x0b, 0x05, 0x00, 0x30, 0x81, 0x93, 0x31, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x46, 0x52,
    0x31, 0x0f, 0x30, 0x0d, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0c, 0x06, 0x46, 0x72, 0x61, 0x6e, 0x63, 0x65, 0x31, 0x11,
    0x30, 0x0f, 0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c, 0x08, 0x53, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x31, 0x36,
    0x30, 0x34, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x2d, 0x53, 0x32, 0x4f, 0x50, 0x43, 0x20, 0x43, 0x65, 0x6e, 0x74,
    0x75, 0x72, 0x79, 0x20, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x20, 0x41, 0x75, 0x74,
    0x68, 0x6f, 0x72, 0x69, 0x74, 0x79, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x54, 0x65, 0x73, 0x74, 0x73, 0x31, 0x28, 0x30,
    0x26, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x01, 0x16, 0x19, 0x73, 0x32, 0x6f, 0x70, 0x63,
    0x2d, 0x73, 0x75, 0x70, 0x70, 0x6f, 0x72, 0x74, 0x40, 0x73, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x2e, 0x66,
    0x72, 0x17, 0x0d, 0x31, 0x38, 0x31, 0x30, 0x30, 0x34, 0x31, 0x35, 0x34, 0x37, 0x35, 0x39, 0x5a, 0x18, 0x0f, 0x32,
    0x31, 0x31, 0x38, 0x30, 0x39, 0x31, 0x30, 0x31, 0x35, 0x34, 0x37, 0x35, 0x39, 0x5a, 0x30, 0x0d, 0x06, 0x09, 0x2a,
    0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x03, 0x82, 0x02, 0x01, 0x00, 0x26, 0xe4, 0x80, 0x22,
    0x70, 0xe2, 0xbc, 0x17, 0x58, 0xd7, 0xa7, 0x52, 0x94, 0x69, 0x21, 0x23, 0xe8, 0x15, 0xf4, 0xe1, 0x30, 0xa2, 0xed,
    0x2e, 0xf0, 0x96, 0xc2, 0x32, 0xb7, 0xce, 0x96, 0x70, 0x0b, 0x37, 0x64, 0x43, 0x13, 0x74, 0xcf, 0xb8, 0xdd, 0xc7,
    0xd2, 0x3d, 0xa5, 0x04, 0xdb, 0xd9, 0xae, 0xbb, 0xa0, 0x6d, 0xb3, 0xd4, 0xe0, 0xd4, 0xdc, 0x57, 0x2b, 0x20, 0x72,
    0x48, 0x56, 0xc8, 0x58, 0xe9, 0xd1, 0x7d, 0x2c, 0xa8, 0x97, 0xcd, 0x60, 0xe3, 0x95, 0x0d, 0x50, 0x8f, 0x56, 0x39,
    0x59, 0x4e, 0x06, 0x6a, 0x1f, 0xef, 0x43, 0x60, 0x74, 0x62, 0x97, 0xc1, 0x7d, 0x4d, 0x2c, 0x1f, 0xf2, 0xaf, 0xb3,
    0xe1, 0x97, 0x1c, 0x87, 0xc1, 0x9d, 0xd7, 0x70, 0x71, 0xec, 0x9f, 0xae, 0x59, 0xab, 0x39, 0x11, 0xb3, 0xb9, 0x3f,
    0x36, 0xf2, 0x66, 0x1e, 0x46, 0xe0, 0xdd, 0xed, 0x53, 0xca, 0x2f, 0xab, 0xc3, 0x6f, 0x35, 0x6b, 0xa3, 0x60, 0x83,
    0x7a, 0xa8, 0xca, 0x67, 0x3c, 0xa7, 0xab, 0x3f, 0x46, 0xfa, 0x1e, 0xe0, 0x41, 0xb7, 0x41, 0x79, 0x6b, 0x9d, 0x30,
    0xe6, 0x40, 0xd8, 0x12, 0xc3, 0x1b, 0x3d, 0x7f, 0x45, 0xb8, 0xa8, 0x60, 0x4d, 0x1a, 0xd1, 0x9f, 0x7a, 0x86, 0x9e,
    0x52, 0x60, 0x89, 0x67, 0xb5, 0xf0, 0xab, 0x73, 0xa8, 0xbd, 0xbb, 0xb0, 0x1c, 0xe4, 0xde, 0xc6, 0xd9, 0x43, 0x8e,
    0xc5, 0xd9, 0x2d, 0xc4, 0x8b, 0xa4, 0xb4, 0x46, 0x1f, 0x9f, 0xc5, 0xf4, 0x36, 0x25, 0xdd, 0x2b, 0xab, 0xdf, 0xd8,
    0x0e, 0x7b, 0xfa, 0xa7, 0x9c, 0x1d, 0xe3, 0x68, 0x02, 0x33, 0xba, 0x8a, 0x32, 0x64, 0x0f, 0x2c, 0x1b, 0x60, 0x56,
    0x39, 0x5a, 0x26, 0x11, 0x98, 0x64, 0x9d, 0x82, 0x73, 0x1f, 0xd8, 0xef, 0x06, 0x97, 0xd5, 0xd4, 0x38, 0x6b, 0xf5,
    0x34, 0xb5, 0xe1, 0x66, 0x1d, 0x56, 0xc5, 0x97, 0x46, 0x65, 0x15, 0x55, 0x45, 0xa7, 0xab, 0x0e, 0xb9, 0xee, 0x89,
    0xf7, 0xca, 0x4a, 0x0d, 0xf9, 0x54, 0x35, 0x5d, 0x69, 0xa0, 0xf1, 0x5f, 0xd2, 0x31, 0x62, 0xe5, 0xc6, 0x31, 0xc4,
    0xe3, 0x0b, 0x95, 0x46, 0xe6, 0xba, 0x70, 0x07, 0x06, 0x80, 0x61, 0xa7, 0xb2, 0x4c, 0x03, 0x79, 0xf2, 0x46, 0x89,
    0xfd, 0xf3, 0xed, 0x69, 0x17, 0xdf, 0x2f, 0x52, 0xb9, 0xe5, 0x36, 0x9f, 0x83, 0x8d, 0x14, 0xa0, 0x19, 0xb1, 0x94,
    0x0a, 0xe1, 0x5d, 0x95, 0x53, 0x5e, 0xb2, 0x3f, 0x71, 0xf1, 0x48, 0x6c, 0x4f, 0xd4, 0x55, 0x67, 0x01, 0x73, 0x9c,
    0x76, 0x19, 0x3c, 0xe1, 0xdf, 0x3b, 0xa3, 0x54, 0xa8, 0x3f, 0x06, 0x53, 0xd2, 0xb9, 0x0b, 0x71, 0xef, 0x4c, 0x3e,
    0xbb, 0x0e, 0xfe, 0x0e, 0xd6, 0x39, 0x0b, 0xf4, 0xd9, 0x2b, 0xc4, 0x52, 0x87, 0x66, 0xf9, 0xcc, 0xa6, 0xe7, 0xa8,
    0x17, 0xbd, 0x1f, 0x3c, 0xdd, 0x30, 0x93, 0x4a, 0x3c, 0x12, 0x2f, 0x41, 0x1b, 0x59, 0x43, 0x36, 0xc7, 0xa5, 0xfb,
    0x4c, 0x1a, 0x78, 0x6b, 0x40, 0xa3, 0x9c, 0x45, 0x8b, 0xc6, 0xa4, 0xaf, 0xed, 0x57, 0x40, 0x9f, 0x75, 0xc5, 0xbe,
    0xd2, 0x3c, 0x37, 0x9c, 0x3f, 0xe9, 0x83, 0x6f, 0x3d, 0xfc, 0xce, 0x1d, 0x64, 0xce, 0xbd, 0x11, 0xcb, 0x51, 0x0a,
    0xe3, 0x19, 0x91, 0x56, 0xea, 0x1a, 0xb2, 0x97, 0x6d, 0xd2, 0xc4, 0x15, 0xa2, 0x29, 0xd8, 0xbc, 0x2a, 0x5a, 0xd4,
    0x75, 0x30, 0x09, 0xf4, 0xdb, 0x48, 0xfa, 0xb7, 0xbe, 0xda, 0xf1, 0xb5, 0x29, 0xbd, 0xe7, 0xbc, 0x73, 0x96, 0xec,
    0x64, 0x03, 0x32, 0xc9, 0x5c, 0xf2, 0x8e, 0x46, 0x19, 0xca, 0xe7, 0x8c, 0x40, 0x54, 0x65, 0x38, 0x32, 0x2d, 0xfe,
    0xea, 0x0f, 0xa3, 0x1d, 0x1a, 0x8a, 0xed, 0xc9, 0xae, 0x42, 0xb5, 0x3a, 0xe8, 0x40};

static const unsigned char server_2k_cert[] = {
    0x30, 0x82, 0x05, 0x13, 0x30, 0x82, 0x02, 0xfb, 0xa0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x01, 0x5b, 0x30, 0x0d, 0x06,
    0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x30, 0x81, 0x93, 0x31, 0x0b, 0x30, 0x09,
    0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x46, 0x52, 0x31, 0x0f, 0x30, 0x0d, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0c,
    0x06, 0x46, 0x72, 0x61, 0x6e, 0x63, 0x65, 0x31, 0x11, 0x30, 0x0f, 0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c, 0x08, 0x53,
    0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x31, 0x36, 0x30, 0x34, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x2d, 0x53,
    0x32, 0x4f, 0x50, 0x43, 0x20, 0x43, 0x65, 0x6e, 0x74, 0x75, 0x72, 0x79, 0x20, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66,
    0x69, 0x63, 0x61, 0x74, 0x65, 0x20, 0x41, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x74, 0x79, 0x20, 0x66, 0x6f, 0x72,
    0x20, 0x54, 0x65, 0x73, 0x74, 0x73, 0x31, 0x28, 0x30, 0x26, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
    0x09, 0x01, 0x16, 0x19, 0x73, 0x32, 0x6f, 0x70, 0x63, 0x2d, 0x73, 0x75, 0x70, 0x70, 0x6f, 0x72, 0x74, 0x40, 0x73,
    0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c, 0x2e, 0x66, 0x72, 0x30, 0x20, 0x17, 0x0d, 0x31, 0x39, 0x31, 0x31, 0x31,
    0x39, 0x31, 0x36, 0x30, 0x36, 0x33, 0x31, 0x5a, 0x18, 0x0f, 0x32, 0x31, 0x31, 0x39, 0x31, 0x30, 0x32, 0x36, 0x31,
    0x36, 0x30, 0x36, 0x33, 0x31, 0x5a, 0x30, 0x66, 0x31, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02,
    0x46, 0x52, 0x31, 0x0f, 0x30, 0x0d, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0c, 0x06, 0x46, 0x72, 0x61, 0x6e, 0x63, 0x65,
    0x31, 0x11, 0x30, 0x0f, 0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c, 0x08, 0x53, 0x79, 0x73, 0x74, 0x65, 0x72, 0x65, 0x6c,
    0x31, 0x33, 0x30, 0x31, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x2a, 0x53, 0x32, 0x4f, 0x50, 0x43, 0x20, 0x43, 0x65,
    0x6e, 0x74, 0x75, 0x72, 0x79, 0x20, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x20, 0x66,
    0x6f, 0x72, 0x20, 0x54, 0x65, 0x73, 0x74, 0x20, 0x53, 0x65, 0x72, 0x76, 0x65, 0x72, 0x73, 0x30, 0x82, 0x01, 0x22,
    0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x82, 0x01, 0x0f,
    0x00, 0x30, 0x82, 0x01, 0x0a, 0x02, 0x82, 0x01, 0x01, 0x00, 0x9b, 0xb3, 0xfc, 0xe0, 0xa5, 0x80, 0x5a, 0x86, 0x80,
    0x35, 0xe5, 0xb1, 0xbb, 0xe1, 0x61, 0xaf, 0x33, 0xbe, 0x45, 0x96, 0xc9, 0x02, 0x9f, 0xe7, 0x28, 0x9e, 0x3c, 0x48,
    0x52, 0xc9, 0xad, 0xa1, 0x05, 0x42, 0x5f, 0x96, 0xbf, 0x73, 0x29, 0x41, 0x12, 0x3e, 0x6d, 0xe1, 0xa7, 0x35, 0xcc,
    0x64, 0x42, 0x29, 0xe8, 0x95, 0xe3, 0x5b, 0xa4, 0x18, 0x0c, 0x37, 0xef, 0xe7, 0x05, 0xf1, 0x37, 0x6b, 0xe6, 0x50,
    0xc8, 0xf4, 0xc6, 0xe1, 0x26, 0xce, 0xa0, 0xf8, 0x0d, 0x52, 0xa0, 0x33, 0xcf, 0x76, 0x83, 0xe1, 0x27, 0xa1, 0xe6,
    0xae, 0x33, 0x6b, 0xb0, 0x78, 0x9c, 0x48, 0xfe, 0x82, 0xbd, 0x0b, 0xc6, 0x5a, 0xc5, 0x33, 0xea, 0x7a, 0x60, 0x57,
    0x39, 0xc0, 0x73, 0x76, 0xce, 0xf6, 0x08, 0x8c, 0xf8, 0x81, 0xee, 0x52, 0xeb, 0x6a, 0xe0, 0x4f, 0xc6, 0xdc, 0x10,
    0xcd, 0x70, 0x59, 0xa1, 0xb8, 0x55, 0x15, 0x31, 0x72, 0x1d, 0x71, 0x48, 0x6b, 0xbb, 0x8f, 0xba, 0x8f, 0x1d, 0x28,
    0x98, 0xcf, 0xca, 0x99, 0x1d, 0xff, 0x31, 0xc7, 0x1d, 0xa7, 0xf7, 0x2b, 0x08, 0x30, 0x3b, 0x45, 0x3f, 0xff, 0xbb,
    0x17, 0x11, 0x17, 0xec, 0xce, 0xd9, 0x33, 0x09, 0x23, 0x3f, 0xe1, 0x17, 0x2f, 0xcb, 0x61, 0x84, 0xb7, 0x6d, 0x6d,
    0x05, 0x56, 0x71, 0xba, 0x56, 0xd2, 0xd5, 0x61, 0xf0, 0x8c, 0xa2, 0x82, 0x8f, 0x97, 0xc7, 0x2c, 0x10, 0x89, 0x9c,
    0x60, 0x31, 0x27, 0xfc, 0x98, 0x72, 0x5a, 0x1b, 0x81, 0x84, 0xa1, 0xa4, 0x9b, 0x84, 0x33, 0x24, 0x00, 0xd2, 0x3d,
    0x92, 0xf3, 0xfd, 0x5a, 0x8b, 0x75, 0x90, 0x5b, 0x3f, 0xac, 0xbb, 0xf7, 0x2e, 0x3b, 0x80, 0xcd, 0xe8, 0x6a, 0xbe,
    0xcf, 0x50, 0x6e, 0x5f, 0x4e, 0x75, 0x1f, 0xe2, 0xfd, 0x3d, 0x16, 0x9e, 0xb0, 0x2d, 0x56, 0x74, 0xef, 0xc6, 0xaf,
    0x02, 0x03, 0x01, 0x00, 0x01, 0xa3, 0x81, 0x9b, 0x30, 0x81, 0x98, 0x30, 0x1d, 0x06, 0x03, 0x55, 0x1d, 0x0e, 0x04,
    0x16, 0x04, 0x14, 0x67, 0x45, 0xaa, 0xcc, 0x41, 0x25, 0x41, 0xd8, 0xe1, 0xd5, 0x50, 0x21, 0xfd, 0x83, 0xe5, 0x77,
    0xa3, 0xf4, 0xe3, 0xea, 0x30, 0x1f, 0x06, 0x03, 0x55, 0x1d, 0x23, 0x04, 0x18, 0x30, 0x16, 0x80, 0x14, 0x7a, 0x46,
    0xcb, 0xd2, 0x2f, 0x30, 0xa4, 0xff, 0x67, 0x29, 0x13, 0x39, 0x3f, 0x9c, 0x02, 0xbf, 0x03, 0xd0, 0x72, 0x82, 0x30,
    0x0b, 0x06, 0x03, 0x55, 0x1d, 0x0f, 0x04, 0x04, 0x03, 0x02, 0x04, 0xf0, 0x30, 0x13, 0x06, 0x03, 0x55, 0x1d, 0x25,
    0x04, 0x0c, 0x30, 0x0a, 0x06, 0x08, 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01, 0x30, 0x09, 0x06, 0x03, 0x55,
    0x1d, 0x13, 0x04, 0x02, 0x30, 0x00, 0x30, 0x29, 0x06, 0x03, 0x55, 0x1d, 0x11, 0x04, 0x22, 0x30, 0x20, 0x86, 0x13,
    0x75, 0x72, 0x6e, 0x3a, 0x53, 0x32, 0x4f, 0x50, 0x43, 0x3a, 0x6c, 0x6f, 0x63, 0x61, 0x6c, 0x68, 0x6f, 0x73, 0x74,
    0x82, 0x09, 0x6c, 0x6f, 0x63, 0x61, 0x6c, 0x68, 0x6f, 0x73, 0x74, 0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86,
    0xf7, 0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00, 0x03, 0x82, 0x02, 0x01, 0x00, 0x09, 0xf2, 0x25, 0x68, 0x1c, 0xa8, 0xf0,
    0xaf, 0xa4, 0x8b, 0x0d, 0x76, 0x25, 0x7c, 0xe2, 0x81, 0xb7, 0x36, 0x10, 0x57, 0xc7, 0xa8, 0xe1, 0x9d, 0xa3, 0xcf,
    0x67, 0xfe, 0x46, 0x73, 0xba, 0xa1, 0x5f, 0xcf, 0x17, 0x15, 0x76, 0xde, 0xe6, 0x8f, 0x37, 0x5c, 0x05, 0x3d, 0xb7,
    0xed, 0x66, 0x06, 0xfc, 0x9b, 0xf4, 0x6b, 0x42, 0xa7, 0x65, 0x63, 0xe9, 0xde, 0x48, 0x50, 0xf1, 0x12, 0x54, 0x01,
    0x06, 0xb8, 0x8d, 0xea, 0x65, 0x2a, 0xed, 0x18, 0x09, 0xda, 0xfb, 0x13, 0xff, 0xbf, 0x17, 0xbb, 0x62, 0xb0, 0x76,
    0x6c, 0xa0, 0xd4, 0x7d, 0x8d, 0x88, 0x6c, 0xd1, 0x9a, 0x1f, 0x75, 0x04, 0xb2, 0x2c, 0x1f, 0xc1, 0x64, 0xff, 0x7f,
    0x85, 0x4d, 0x7e, 0x44, 0x77, 0x5c, 0x53, 0xc6, 0xcf, 0xdd, 0x1f, 0x03, 0xde, 0xf6, 0xb5, 0x7c, 0x32, 0x3c, 0x3e,
    0x13, 0x50, 0x36, 0x02, 0xa9, 0x74, 0x08, 0x80, 0x80, 0x8a, 0xa3, 0x5b, 0x07, 0x32, 0x00, 0x53, 0x10, 0x44, 0x60,
    0x3b, 0x25, 0xa2, 0x9a, 0xf7, 0x62, 0x30, 0x68, 0x26, 0x1f, 0xdd, 0x57, 0xb8, 0x6c, 0x3d, 0xfb, 0x85, 0xe5, 0xab,
    0x51, 0x04, 0x50, 0x6e, 0x9d, 0xed, 0x22, 0x6e, 0x5c, 0x8c, 0x58, 0x0e, 0x80, 0xa0, 0xb9, 0xd2, 0xb4, 0xd2, 0x5d,
    0x5c, 0xed, 0xbe, 0x01, 0x1c, 0x01, 0xac, 0x9a, 0xdc, 0x68, 0x67, 0x81, 0x93, 0x1a, 0x87, 0xd1, 0xeb, 0xb5, 0x57,
    0x73, 0xef, 0x71, 0xe8, 0x34, 0x17, 0x4c, 0xf4, 0x46, 0x25, 0x45, 0xd6, 0xad, 0x36, 0x97, 0xd9, 0x09, 0xc4, 0x33,
    0x0f, 0x56, 0xf4, 0x74, 0x16, 0xc4, 0x09, 0x26, 0x0a, 0x57, 0xdd, 0x01, 0xcb, 0xe1, 0x82, 0x17, 0xa7, 0x3c, 0xe1,
    0x2e, 0x0f, 0xe0, 0x1e, 0xed, 0x4b, 0x21, 0xd4, 0x3e, 0x80, 0x53, 0x95, 0xf3, 0xa3, 0xa4, 0x04, 0xb6, 0x5d, 0x5c,
    0xd3, 0xa0, 0xd5, 0x7c, 0xbb, 0xfc, 0xb6, 0xac, 0xd9, 0x70, 0x64, 0xcc, 0xe3, 0xab, 0xb0, 0x87, 0xd5, 0x66, 0x48,
    0x7e, 0xc6, 0x86, 0xab, 0xce, 0x7e, 0x9d, 0xd7, 0x07, 0xec, 0xc1, 0x3b, 0x91, 0xb0, 0x10, 0xd9, 0xfb, 0xbd, 0xd5,
    0x77, 0x2c, 0x2d, 0xb4, 0x88, 0xb5, 0x24, 0x2b, 0xbe, 0x87, 0xed, 0xd5, 0xda, 0xed, 0xf3, 0x89, 0x35, 0x3a, 0xaa,
    0x22, 0x5b, 0xbb, 0xf8, 0x33, 0x6a, 0x79, 0xd1, 0x9f, 0x9d, 0xe9, 0x7b, 0xcd, 0x83, 0x95, 0x7b, 0xca, 0x12, 0xc6,
    0x60, 0x29, 0x66, 0x63, 0x49, 0xaa, 0xca, 0xfa, 0xdf, 0x08, 0x9d, 0xb5, 0x3d, 0x20, 0xf9, 0x33, 0x14, 0x6a, 0xb5,
    0xaa, 0xa0, 0x5c, 0xaa, 0x9b, 0x76, 0xc4, 0x80, 0x17, 0x86, 0xf1, 0x9d, 0xa9, 0xd7, 0xa5, 0xf5, 0x09, 0xec, 0x34,
    0x21, 0xd0, 0xe1, 0x92, 0xda, 0x13, 0x31, 0xfb, 0xa8, 0xdb, 0xd9, 0xaa, 0xd9, 0xcc, 0x85, 0x87, 0x20, 0x96, 0x3a,
    0xc5, 0xfc, 0x51, 0xb9, 0x92, 0xee, 0x87, 0x76, 0x88, 0xee, 0x42, 0x88, 0x53, 0x12, 0x69, 0x05, 0x7b, 0x2d, 0x92,
    0xb9, 0x74, 0x61, 0x8a, 0xf8, 0xaa, 0x19, 0x62, 0x1d, 0x4d, 0xea, 0x83, 0x78, 0x09, 0xf2, 0x3e, 0xd7, 0xee, 0xac,
    0x38, 0xf9, 0x0a, 0x26, 0x5c, 0xde, 0xda, 0xf6, 0xeb, 0x01, 0xc8, 0x22, 0x47, 0xd5, 0xe0, 0xae, 0x30, 0x90, 0x5c,
    0x16, 0x63, 0x35, 0x60, 0xf7, 0x40, 0x5b, 0x1d, 0xb6, 0x58, 0x32, 0x12, 0x1f, 0xe8, 0x84, 0xd5, 0x40, 0xa2, 0x93,
    0x23, 0xa8, 0x95, 0x2d, 0x72, 0x6e, 0x91, 0x39, 0xee, 0x6f, 0x29, 0xad, 0xcd, 0x76, 0xba, 0xb7, 0x19, 0x7b, 0xea,
    0x16, 0x51, 0x1f, 0x90, 0x79, 0xf5, 0x0f, 0xe8, 0x93, 0x5c, 0x18, 0x41, 0x74, 0x32, 0x4d, 0xba, 0x24, 0x1a, 0x3b,
    0x6f, 0x0d, 0x40, 0xe8, 0xe4, 0xe0, 0x43, 0x19, 0xa3, 0x37, 0xdc};

static const unsigned char server_2k_key[] = {
    0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x42, 0x45, 0x47, 0x49, 0x4e, 0x20, 0x50, 0x52, 0x49, 0x56, 0x41, 0x54, 0x45, 0x20,
    0x4b, 0x45, 0x59, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x0a, 0x4d, 0x49, 0x49, 0x45, 0x76, 0x67, 0x49, 0x42, 0x41, 0x44,
    0x41, 0x4e, 0x42, 0x67, 0x6b, 0x71, 0x68, 0x6b, 0x69, 0x47, 0x39, 0x77, 0x30, 0x42, 0x41, 0x51, 0x45, 0x46, 0x41,
    0x41, 0x53, 0x43, 0x42, 0x4b, 0x67, 0x77, 0x67, 0x67, 0x53, 0x6b, 0x41, 0x67, 0x45, 0x41, 0x41, 0x6f, 0x49, 0x42,
    0x41, 0x51, 0x43, 0x62, 0x73, 0x2f, 0x7a, 0x67, 0x70, 0x59, 0x42, 0x61, 0x68, 0x6f, 0x41, 0x31, 0x0a, 0x35, 0x62,
    0x47, 0x37, 0x34, 0x57, 0x47, 0x76, 0x4d, 0x37, 0x35, 0x46, 0x6c, 0x73, 0x6b, 0x43, 0x6e, 0x2b, 0x63, 0x6f, 0x6e,
    0x6a, 0x78, 0x49, 0x55, 0x73, 0x6d, 0x74, 0x6f, 0x51, 0x56, 0x43, 0x58, 0x35, 0x61, 0x2f, 0x63, 0x79, 0x6c, 0x42,
    0x45, 0x6a, 0x35, 0x74, 0x34, 0x61, 0x63, 0x31, 0x7a, 0x47, 0x52, 0x43, 0x4b, 0x65, 0x69, 0x56, 0x34, 0x31, 0x75,
    0x6b, 0x47, 0x41, 0x77, 0x33, 0x0a, 0x37, 0x2b, 0x63, 0x46, 0x38, 0x54, 0x64, 0x72, 0x35, 0x6c, 0x44, 0x49, 0x39,
    0x4d, 0x62, 0x68, 0x4a, 0x73, 0x36, 0x67, 0x2b, 0x41, 0x31, 0x53, 0x6f, 0x44, 0x50, 0x50, 0x64, 0x6f, 0x50, 0x68,
    0x4a, 0x36, 0x48, 0x6d, 0x72, 0x6a, 0x4e, 0x72, 0x73, 0x48, 0x69, 0x63, 0x53, 0x50, 0x36, 0x43, 0x76, 0x51, 0x76,
    0x47, 0x57, 0x73, 0x55, 0x7a, 0x36, 0x6e, 0x70, 0x67, 0x56, 0x7a, 0x6e, 0x41, 0x0a, 0x63, 0x33, 0x62, 0x4f, 0x39,
    0x67, 0x69, 0x4d, 0x2b, 0x49, 0x48, 0x75, 0x55, 0x75, 0x74, 0x71, 0x34, 0x45, 0x2f, 0x47, 0x33, 0x42, 0x44, 0x4e,
    0x63, 0x46, 0x6d, 0x68, 0x75, 0x46, 0x55, 0x56, 0x4d, 0x58, 0x49, 0x64, 0x63, 0x55, 0x68, 0x72, 0x75, 0x34, 0x2b,
    0x36, 0x6a, 0x78, 0x30, 0x6f, 0x6d, 0x4d, 0x2f, 0x4b, 0x6d, 0x52, 0x33, 0x2f, 0x4d, 0x63, 0x63, 0x64, 0x70, 0x2f,
    0x63, 0x72, 0x0a, 0x43, 0x44, 0x41, 0x37, 0x52, 0x54, 0x2f, 0x2f, 0x75, 0x78, 0x63, 0x52, 0x46, 0x2b, 0x7a, 0x4f,
    0x32, 0x54, 0x4d, 0x4a, 0x49, 0x7a, 0x2f, 0x68, 0x46, 0x79, 0x2f, 0x4c, 0x59, 0x59, 0x53, 0x33, 0x62, 0x57, 0x30,
    0x46, 0x56, 0x6e, 0x47, 0x36, 0x56, 0x74, 0x4c, 0x56, 0x59, 0x66, 0x43, 0x4d, 0x6f, 0x6f, 0x4b, 0x50, 0x6c, 0x38,
    0x63, 0x73, 0x45, 0x49, 0x6d, 0x63, 0x59, 0x44, 0x45, 0x6e, 0x0a, 0x2f, 0x4a, 0x68, 0x79, 0x57, 0x68, 0x75, 0x42,
    0x68, 0x4b, 0x47, 0x6b, 0x6d, 0x34, 0x51, 0x7a, 0x4a, 0x41, 0x44, 0x53, 0x50, 0x5a, 0x4c, 0x7a, 0x2f, 0x56, 0x71,
    0x4c, 0x64, 0x5a, 0x42, 0x62, 0x50, 0x36, 0x79, 0x37, 0x39, 0x79, 0x34, 0x37, 0x67, 0x4d, 0x33, 0x6f, 0x61, 0x72,
    0x37, 0x50, 0x55, 0x47, 0x35, 0x66, 0x54, 0x6e, 0x55, 0x66, 0x34, 0x76, 0x30, 0x39, 0x46, 0x70, 0x36, 0x77, 0x0a,
    0x4c, 0x56, 0x5a, 0x30, 0x37, 0x38, 0x61, 0x76, 0x41, 0x67, 0x4d, 0x42, 0x41, 0x41, 0x45, 0x43, 0x67, 0x67, 0x45,
    0x42, 0x41, 0x4a, 0x6f, 0x35, 0x72, 0x77, 0x71, 0x4a, 0x68, 0x46, 0x69, 0x6d, 0x6a, 0x30, 0x70, 0x54, 0x71, 0x54,
    0x67, 0x54, 0x5a, 0x2b, 0x48, 0x56, 0x32, 0x2b, 0x73, 0x73, 0x44, 0x78, 0x44, 0x31, 0x65, 0x45, 0x39, 0x6f, 0x5a,
    0x51, 0x65, 0x79, 0x55, 0x53, 0x67, 0x56, 0x0a, 0x72, 0x5a, 0x4c, 0x77, 0x41, 0x65, 0x37, 0x43, 0x30, 0x43, 0x4d,
    0x76, 0x51, 0x66, 0x30, 0x76, 0x48, 0x61, 0x51, 0x52, 0x50, 0x32, 0x47, 0x32, 0x42, 0x7a, 0x61, 0x6f, 0x6a, 0x48,
    0x59, 0x2b, 0x68, 0x36, 0x50, 0x45, 0x6b, 0x6b, 0x33, 0x31, 0x66, 0x31, 0x4c, 0x32, 0x51, 0x43, 0x43, 0x39, 0x4c,
    0x46, 0x32, 0x4b, 0x52, 0x66, 0x4e, 0x31, 0x6f, 0x43, 0x53, 0x75, 0x6f, 0x49, 0x4d, 0x6e, 0x0a, 0x76, 0x6a, 0x75,
    0x41, 0x4f, 0x55, 0x4b, 0x34, 0x58, 0x43, 0x43, 0x59, 0x48, 0x4f, 0x2b, 0x59, 0x38, 0x64, 0x68, 0x6f, 0x44, 0x73,
    0x69, 0x37, 0x30, 0x6b, 0x65, 0x35, 0x51, 0x74, 0x77, 0x34, 0x71, 0x66, 0x43, 0x78, 0x72, 0x67, 0x59, 0x54, 0x39,
    0x36, 0x5a, 0x43, 0x35, 0x4e, 0x67, 0x2b, 0x39, 0x41, 0x62, 0x61, 0x42, 0x73, 0x74, 0x50, 0x34, 0x61, 0x6a, 0x4d,
    0x56, 0x30, 0x76, 0x79, 0x0a, 0x4d, 0x57, 0x39, 0x6d, 0x6f, 0x58, 0x38, 0x72, 0x54, 0x74, 0x34, 0x33, 0x56, 0x34,
    0x6e, 0x59, 0x72, 0x66, 0x71, 0x7a, 0x6a, 0x66, 0x42, 0x7a, 0x72, 0x31, 0x43, 0x78, 0x6c, 0x75, 0x77, 0x33, 0x4f,
    0x69, 0x4a, 0x6d, 0x6a, 0x79, 0x58, 0x72, 0x61, 0x6a, 0x56, 0x35, 0x38, 0x74, 0x6a, 0x62, 0x2b, 0x6e, 0x4f, 0x39,
    0x4d, 0x4d, 0x53, 0x44, 0x6f, 0x73, 0x78, 0x68, 0x4c, 0x46, 0x78, 0x4d, 0x0a, 0x61, 0x73, 0x41, 0x42, 0x46, 0x44,
    0x4a, 0x45, 0x58, 0x2f, 0x57, 0x66, 0x6a, 0x67, 0x42, 0x62, 0x52, 0x70, 0x71, 0x6f, 0x68, 0x78, 0x38, 0x73, 0x42,
    0x41, 0x2b, 0x6f, 0x35, 0x50, 0x62, 0x49, 0x68, 0x55, 0x2f, 0x68, 0x4d, 0x49, 0x58, 0x59, 0x79, 0x74, 0x64, 0x4d,
    0x69, 0x42, 0x6a, 0x69, 0x33, 0x68, 0x64, 0x73, 0x64, 0x4e, 0x63, 0x71, 0x50, 0x53, 0x69, 0x68, 0x50, 0x53, 0x37,
    0x67, 0x0a, 0x73, 0x48, 0x69, 0x49, 0x68, 0x38, 0x6c, 0x35, 0x38, 0x42, 0x39, 0x55, 0x61, 0x4a, 0x65, 0x32, 0x30,
    0x47, 0x6b, 0x75, 0x76, 0x6c, 0x58, 0x6d, 0x62, 0x68, 0x4d, 0x6d, 0x66, 0x73, 0x43, 0x75, 0x63, 0x62, 0x4e, 0x71,
    0x46, 0x7a, 0x61, 0x50, 0x69, 0x78, 0x6b, 0x43, 0x67, 0x59, 0x45, 0x41, 0x79, 0x6c, 0x75, 0x75, 0x52, 0x37, 0x7a,
    0x51, 0x4e, 0x6f, 0x47, 0x6c, 0x35, 0x67, 0x6c, 0x37, 0x0a, 0x45, 0x68, 0x61, 0x43, 0x65, 0x77, 0x4a, 0x33, 0x70,
    0x75, 0x47, 0x32, 0x4d, 0x67, 0x33, 0x52, 0x58, 0x79, 0x48, 0x33, 0x58, 0x38, 0x39, 0x30, 0x71, 0x4d, 0x7a, 0x72,
    0x4a, 0x36, 0x46, 0x4c, 0x36, 0x71, 0x59, 0x59, 0x5a, 0x4e, 0x71, 0x31, 0x39, 0x66, 0x66, 0x50, 0x42, 0x4a, 0x4d,
    0x6e, 0x43, 0x4c, 0x2b, 0x4e, 0x51, 0x4f, 0x59, 0x67, 0x35, 0x73, 0x6d, 0x65, 0x6b, 0x4f, 0x2f, 0x55, 0x0a, 0x64,
    0x2f, 0x4d, 0x72, 0x64, 0x35, 0x31, 0x2b, 0x4f, 0x77, 0x7a, 0x72, 0x39, 0x46, 0x58, 0x50, 0x48, 0x77, 0x42, 0x4c,
    0x48, 0x32, 0x44, 0x74, 0x70, 0x4a, 0x39, 0x41, 0x69, 0x70, 0x33, 0x76, 0x31, 0x42, 0x43, 0x4f, 0x56, 0x4e, 0x52,
    0x49, 0x7a, 0x56, 0x66, 0x43, 0x44, 0x4b, 0x47, 0x57, 0x79, 0x5a, 0x74, 0x37, 0x53, 0x63, 0x79, 0x66, 0x2f, 0x66,
    0x5a, 0x7a, 0x66, 0x46, 0x45, 0x61, 0x0a, 0x37, 0x4b, 0x4f, 0x30, 0x52, 0x67, 0x67, 0x4c, 0x6f, 0x71, 0x68, 0x4e,
    0x65, 0x48, 0x56, 0x31, 0x46, 0x62, 0x43, 0x61, 0x33, 0x6b, 0x4b, 0x62, 0x36, 0x6f, 0x55, 0x43, 0x67, 0x59, 0x45,
    0x41, 0x78, 0x50, 0x6f, 0x36, 0x46, 0x54, 0x4a, 0x7a, 0x50, 0x72, 0x63, 0x39, 0x48, 0x4b, 0x47, 0x31, 0x69, 0x77,
    0x49, 0x4e, 0x35, 0x37, 0x4f, 0x45, 0x31, 0x32, 0x6d, 0x7a, 0x6b, 0x55, 0x44, 0x4c, 0x0a, 0x4d, 0x77, 0x74, 0x30,
    0x36, 0x37, 0x57, 0x48, 0x32, 0x4a, 0x75, 0x57, 0x38, 0x64, 0x33, 0x69, 0x4f, 0x73, 0x42, 0x51, 0x30, 0x67, 0x59,
    0x4b, 0x36, 0x2f, 0x74, 0x71, 0x4c, 0x76, 0x33, 0x6f, 0x4f, 0x32, 0x54, 0x50, 0x6d, 0x4c, 0x5a, 0x48, 0x62, 0x78,
    0x30, 0x34, 0x73, 0x64, 0x55, 0x73, 0x64, 0x6c, 0x44, 0x2b, 0x47, 0x38, 0x35, 0x4d, 0x6b, 0x4b, 0x56, 0x78, 0x61,
    0x51, 0x53, 0x48, 0x0a, 0x5a, 0x4a, 0x55, 0x2b, 0x75, 0x45, 0x7a, 0x47, 0x48, 0x71, 0x34, 0x32, 0x63, 0x6f, 0x6b,
    0x38, 0x63, 0x6b, 0x39, 0x52, 0x6f, 0x37, 0x49, 0x31, 0x38, 0x32, 0x56, 0x74, 0x2b, 0x41, 0x42, 0x5a, 0x62, 0x76,
    0x43, 0x4a, 0x73, 0x54, 0x78, 0x47, 0x46, 0x69, 0x2b, 0x43, 0x69, 0x41, 0x41, 0x73, 0x79, 0x68, 0x44, 0x30, 0x56,
    0x37, 0x32, 0x5a, 0x54, 0x6b, 0x68, 0x61, 0x59, 0x47, 0x6b, 0x37, 0x0a, 0x57, 0x4c, 0x71, 0x66, 0x61, 0x2f, 0x30,
    0x50, 0x35, 0x4b, 0x4d, 0x43, 0x67, 0x59, 0x45, 0x41, 0x6b, 0x4c, 0x30, 0x61, 0x33, 0x7a, 0x7a, 0x79, 0x51, 0x4d,
    0x70, 0x69, 0x2b, 0x7a, 0x4c, 0x30, 0x30, 0x47, 0x39, 0x42, 0x54, 0x50, 0x4c, 0x71, 0x32, 0x6e, 0x61, 0x2f, 0x64,
    0x76, 0x58, 0x6a, 0x4f, 0x41, 0x52, 0x33, 0x69, 0x42, 0x51, 0x2f, 0x41, 0x53, 0x33, 0x78, 0x56, 0x52, 0x74, 0x4e,
    0x0a, 0x7a, 0x62, 0x79, 0x58, 0x33, 0x69, 0x75, 0x42, 0x30, 0x7a, 0x6b, 0x34, 0x33, 0x62, 0x44, 0x54, 0x54, 0x72,
    0x4b, 0x55, 0x4f, 0x6b, 0x4e, 0x67, 0x62, 0x54, 0x4c, 0x78, 0x4e, 0x41, 0x49, 0x58, 0x47, 0x75, 0x54, 0x58, 0x78,
    0x6d, 0x72, 0x6b, 0x43, 0x79, 0x43, 0x6d, 0x39, 0x4e, 0x45, 0x62, 0x6f, 0x4c, 0x54, 0x35, 0x42, 0x71, 0x79, 0x78,
    0x7a, 0x66, 0x6f, 0x4b, 0x6c, 0x42, 0x74, 0x37, 0x0a, 0x6d, 0x31, 0x64, 0x73, 0x4e, 0x73, 0x6a, 0x51, 0x65, 0x65,
    0x2b, 0x33, 0x59, 0x49, 0x6d, 0x44, 0x37, 0x52, 0x68, 0x46, 0x43, 0x76, 0x68, 0x4e, 0x78, 0x37, 0x30, 0x72, 0x78,
    0x56, 0x50, 0x4e, 0x79, 0x6b, 0x30, 0x64, 0x65, 0x4b, 0x6e, 0x77, 0x69, 0x4a, 0x75, 0x52, 0x4c, 0x67, 0x50, 0x31,
    0x68, 0x31, 0x6f, 0x57, 0x71, 0x37, 0x74, 0x42, 0x41, 0x6e, 0x45, 0x43, 0x67, 0x59, 0x42, 0x37, 0x0a, 0x61, 0x6d,
    0x53, 0x56, 0x2f, 0x32, 0x51, 0x68, 0x75, 0x57, 0x46, 0x36, 0x33, 0x50, 0x38, 0x49, 0x4e, 0x36, 0x4e, 0x4b, 0x74,
    0x7a, 0x6e, 0x57, 0x56, 0x67, 0x34, 0x43, 0x52, 0x6c, 0x79, 0x4b, 0x67, 0x50, 0x55, 0x69, 0x38, 0x6a, 0x78, 0x4a,
    0x52, 0x55, 0x4d, 0x51, 0x43, 0x2f, 0x76, 0x41, 0x33, 0x39, 0x70, 0x44, 0x6e, 0x54, 0x47, 0x65, 0x70, 0x59, 0x6e,
    0x6b, 0x49, 0x34, 0x59, 0x73, 0x0a, 0x49, 0x48, 0x2f, 0x4a, 0x71, 0x50, 0x75, 0x63, 0x37, 0x4f, 0x77, 0x6d, 0x7a,
    0x2b, 0x2f, 0x70, 0x75, 0x64, 0x6c, 0x63, 0x78, 0x71, 0x64, 0x47, 0x51, 0x63, 0x4b, 0x4c, 0x45, 0x43, 0x46, 0x63,
    0x72, 0x66, 0x33, 0x38, 0x4c, 0x32, 0x34, 0x36, 0x72, 0x75, 0x44, 0x43, 0x5a, 0x71, 0x59, 0x4f, 0x34, 0x51, 0x2b,
    0x2f, 0x78, 0x74, 0x72, 0x79, 0x77, 0x32, 0x78, 0x68, 0x5a, 0x4b, 0x61, 0x6b, 0x0a, 0x55, 0x65, 0x57, 0x54, 0x76,
    0x4c, 0x59, 0x56, 0x46, 0x48, 0x4e, 0x75, 0x6a, 0x74, 0x32, 0x42, 0x52, 0x5a, 0x6f, 0x79, 0x6c, 0x30, 0x4c, 0x45,
    0x76, 0x36, 0x53, 0x51, 0x6e, 0x35, 0x35, 0x6c, 0x65, 0x35, 0x69, 0x44, 0x61, 0x71, 0x31, 0x59, 0x6a, 0x51, 0x4b,
    0x42, 0x67, 0x42, 0x59, 0x48, 0x70, 0x72, 0x68, 0x57, 0x42, 0x36, 0x70, 0x37, 0x6d, 0x79, 0x4f, 0x34, 0x77, 0x4f,
    0x48, 0x6c, 0x0a, 0x30, 0x5a, 0x48, 0x32, 0x43, 0x2f, 0x33, 0x4c, 0x79, 0x35, 0x58, 0x35, 0x41, 0x37, 0x36, 0x62,
    0x75, 0x6c, 0x61, 0x51, 0x54, 0x37, 0x59, 0x4b, 0x64, 0x6a, 0x67, 0x67, 0x76, 0x76, 0x78, 0x50, 0x74, 0x41, 0x75,
    0x36, 0x63, 0x49, 0x34, 0x31, 0x6c, 0x36, 0x45, 0x65, 0x4d, 0x30, 0x66, 0x6e, 0x69, 0x6f, 0x45, 0x77, 0x52, 0x5a,
    0x73, 0x65, 0x45, 0x57, 0x79, 0x6f, 0x55, 0x4d, 0x58, 0x2b, 0x0a, 0x4b, 0x69, 0x33, 0x70, 0x2f, 0x74, 0x53, 0x5a,
    0x53, 0x5a, 0x61, 0x35, 0x70, 0x5a, 0x47, 0x2f, 0x62, 0x45, 0x59, 0x4c, 0x52, 0x68, 0x72, 0x66, 0x50, 0x47, 0x2b,
    0x4c, 0x47, 0x54, 0x4a, 0x2f, 0x37, 0x68, 0x6c, 0x41, 0x75, 0x59, 0x77, 0x44, 0x35, 0x47, 0x72, 0x6c, 0x72, 0x62,
    0x65, 0x38, 0x52, 0x32, 0x56, 0x77, 0x35, 0x41, 0x73, 0x70, 0x77, 0x38, 0x61, 0x62, 0x4b, 0x76, 0x44, 0x77, 0x0a,
    0x6a, 0x62, 0x45, 0x6f, 0x65, 0x66, 0x46, 0x77, 0x56, 0x63, 0x55, 0x2f, 0x41, 0x33, 0x76, 0x71, 0x63, 0x70, 0x50,
    0x72, 0x33, 0x61, 0x62, 0x59, 0x0a, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x45, 0x4e, 0x44, 0x20, 0x50, 0x52, 0x49, 0x56,
    0x41, 0x54, 0x45, 0x20, 0x4b, 0x45, 0x59, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x0a};

static const unsigned char pubSub_keySign[] = {0xE9, 0x65, 0x4E, 0x23, 0x46, 0x1A, 0xC8, 0xAB, 0x58, 0x4F, 0x7F,
                                               0x6B, 0x99, 0x1E, 0x75, 0x2E, 0xA5, 0x82, 0xAC, 0xD2, 0x61, 0x5A,
                                               0x92, 0xC1, 0x37, 0x22, 0x04, 0xC9, 0x96, 0x1C, 0x18, 0x4C};

static const unsigned char pubSub_keyEncrypt[] = {0xA5, 0x82, 0xAC, 0xD2, 0x61, 0x5A, 0x92, 0xC1, 0x37, 0x22, 0x04,
                                                  0xC9, 0x96, 0x1C, 0x18, 0x4C, 0xE9, 0x65, 0x4E, 0x23, 0x46, 0x1A,
                                                  0xC8, 0xAB, 0x58, 0x4F, 0x7F, 0x6B, 0x99, 0x1E, 0x75, 0x2E};

static const unsigned char pubSub_keyNonce[] = {0xB3, 0x83, 0x00, 0x00};

#endif
