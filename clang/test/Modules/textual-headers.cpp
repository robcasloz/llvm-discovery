// RUN: rm -rf %t
// RUN: %clang_cc1 -fmodule-maps -fmodules-cache-path=%t -fmodules-strict-decluse -fmodule-name=XG -I %S/Inputs/declare-use %s -verify
// RUN: %clang_cc1 -fmodules -fmodules-cache-path=%t -fmodules-strict-decluse -fmodule-name=XG -I %S/Inputs/declare-use %s -verify -fmodules-no-error-recovery

#define GIMME_A_K
#include "k.h"

#define GIMME_AN_L
#include "l.h" // expected-error {{module XG does not depend on a module exporting 'l.h'}}

#include "m2.h" // expected-error {{module XG does not depend on a module exporting 'm2.h'}}
const int use_m = m;

#define GIMME_AN_M
#include "m.h"
const int use_m_2 = m;

const int g = k + l;
