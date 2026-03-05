int main1(int i){
  int mf7, m;
  mf7=23;
  m=mf7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == mf7;
  loop invariant i >= \at(i, Pre);
  loop invariant m > 0;
  loop invariant (i - \at(i,Pre)) % m == 0;
  loop assigns i, m;
*/
while (m<mf7&&m>0) {
      m++;
      m -= 1;
      i = i + m;
  }
}