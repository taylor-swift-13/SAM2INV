int main1(int m){
  int b, k, j, v;

  b=m;
  k=0;
  j=m;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m,Pre);
  loop invariant b == \at(m,Pre);
  loop invariant j <= b;
  loop invariant b == m;
  loop invariant j >= m;
  loop invariant j >= \at(m, Pre);
  loop assigns j;
*/
while (j<b) {
      if (j<b) {
          j = j+1;
      }
  }

}
