int main1(int s,int i){
  int j, hr;
  j=(s%7)+14;
  hr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre);
  loop invariant j == (\at(s, Pre) % 7) + 14;
  loop invariant (s - \at(s, Pre)) % j == 0;
  loop invariant s >= \at(s,Pre);
  loop invariant hr >= 0;
  loop assigns hr, s;
*/
while (hr!=hr) {
      hr = hr;
      hr = (hr+j/hr)/2;
      s += j;
  }
}