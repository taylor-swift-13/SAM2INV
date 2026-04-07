int main1(int o){
  int x5n, mx2, k2j;
  x5n=o*2;
  mx2=0;
  k2j=x5n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x5n == 2 * \at(o, Pre);
  loop invariant o == \at(o, Pre) + (mx2 * (mx2 + 1)) / 2;
  loop invariant k2j == \at(o, Pre) * (2 + mx2) + (mx2 * (mx2 - 1) * (mx2 + 1)) / 6;
  loop invariant k2j == \at(o, Pre) * (mx2 + 2) + ((mx2 - 1) * mx2 * (mx2 + 1)) / 6;
  loop invariant 2 * (o - \at(o, Pre)) == (mx2 * (mx2 + 1));
  loop invariant 6 * (k2j - \at(o, Pre) * (mx2 + 2)) == (mx2 * (mx2 - 1) * (mx2 + 1));
  loop invariant mx2 >= 0;
  loop invariant (x5n >= 0) ==> (mx2 <= x5n);
  loop invariant k2j == (2 + mx2) * \at(o,Pre)
                       + ( (mx2 * (mx2 - 1) * (mx2 + 1)) / 6 );
  loop invariant (x5n == 2 * \at(o, Pre));
  loop invariant (mx2 >= 0);
  loop assigns k2j, mx2, o;
*/
while (mx2 < x5n) {
      k2j = k2j + o;
      mx2 = mx2 + 1;
      o = o + mx2;
  }
}