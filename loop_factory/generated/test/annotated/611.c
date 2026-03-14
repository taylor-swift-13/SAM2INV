int main1(){
  int l8s, q3cz, xi2, a7;
  l8s=1-4;
  q3cz=l8s;
  xi2=13;
  a7=l8s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q3cz == l8s || q3cz == 1;
  loop invariant xi2 >= 10;
  loop invariant l8s == 1 - 4;
  loop invariant a7 == l8s;
  loop invariant xi2 <= 14;
  loop assigns xi2, q3cz;
*/
while (q3cz>1) {
      if (!(!(q3cz<l8s/2))) {
          xi2 += 1;
      }
      else {
          xi2 += a7;
      }
      q3cz = 1;
  }
}