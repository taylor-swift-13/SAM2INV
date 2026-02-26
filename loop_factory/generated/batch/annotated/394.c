int main1(int m,int p){
  int b, k, j, v;

  b=p;
  k=0;
  j=p;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == p;
  loop invariant j <= b;
  loop invariant j >= p;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(p, Pre);
  loop invariant j >= \at(p, Pre);
  loop invariant j == p;
  loop assigns j;
*/
while (j<b) {
      if (j<b) {
          j = j+1;
      }
  }

}
