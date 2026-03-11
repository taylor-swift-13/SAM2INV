int main1(){
  int z6sv, sk, cf, pt;
  z6sv=1;
  sk=z6sv;
  cf=4;
  pt=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z6sv == 1;
  loop invariant sk <= z6sv;
  loop invariant cf == 4 + 6*(sk - 1);
  loop invariant pt == 10 + 6*(sk - 1);
  loop assigns cf, pt, sk;
*/
while (1) {
      if (!(sk<=z6sv-1)) {
          break;
      }
      cf += 6;
      pt += 6;
      sk = sk + 1;
  }
}