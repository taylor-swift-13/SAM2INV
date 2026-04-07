int main1(){
  int e, v9, oufi, m, py0, y, dvp, ru3;
  e=1+8;
  v9=3;
  oufi=v9;
  m=e;
  py0=6;
  y=6;
  dvp=v9;
  ru3=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e >= v9 + 4;
  loop invariant py0 <= y;
  loop invariant v9 == 3;
  loop invariant py0 >= 6;
  loop invariant m >= 9;
  loop invariant y >= 6;
  loop invariant (y % 2) == 0;
  loop invariant ru3 - y == 3;
  loop invariant dvp == 3;
  loop invariant (e == 9) || (e == v9 + 4);
  loop invariant oufi >= 3;
  loop invariant m >= oufi;
  loop assigns e, m, oufi, dvp, ru3, py0, y;
*/
while (v9+5<=e) {
      if (!(!(v9<e/2))) {
          oufi = oufi + 1;
      }
      else {
          oufi = oufi + m;
      }
      if (v9+4<=dvp+e) {
          dvp = v9;
      }
      m = m + oufi;
      ru3 += 2;
      py0 = py0+(v9%2);
      y += 2;
      e = (v9+5)-1;
  }
}