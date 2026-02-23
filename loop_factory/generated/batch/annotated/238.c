int main1(int b,int k){
  int v, o, j, z;

  v=b;
  o=v;
  j=o;
  z=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == b;
  loop invariant j <= v;
  loop invariant j >= b;
  loop invariant (j - b) % 2 == 0;
  loop invariant v == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (v - j) % 2 == 0;
  loop invariant j <= v + 1;
  loop invariant b == \at(b,Pre);
  loop invariant (j - \at(b, Pre)) % 2 == 0;
  loop invariant j >= \at(b, Pre);
  loop assigns j;
*/
while (j<v) {
      if (j<v) {
          j = j+1;
      }
      j = j+1;
  }

}
