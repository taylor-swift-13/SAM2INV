int main1(int u){
  int y34s, kv9, zv9;
  y34s=u+4;
  kv9=y34s;
  zv9=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u >= \at(u, Pre);
  loop invariant zv9 >= 3;
  loop invariant kv9 == \at(u, Pre) + 4;
  loop invariant y34s == \at(u, Pre) + 4;
  loop assigns u, zv9;
*/
while (kv9>=2) {
      zv9 = zv9 + 1;
      zv9 = zv9 + zv9;
      u = u + zv9;
  }
}