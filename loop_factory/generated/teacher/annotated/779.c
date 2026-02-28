int main1(int m,int p){
  int n, y, v, l;

  n=(m%39)+18;
  y=0;
  v=m;
  l=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == m + 6*y;

  loop invariant (y % 2 == 0) ==> (l == m + 3*y);
  loop invariant (y % 2 == 1) ==> (l == 3*y - 1);
  loop invariant 0 <= y;
  loop invariant n == (\at(m,Pre) % 39) + 18;
  loop invariant m == \at(m,Pre);
  loop invariant p == \at(p,Pre);


  loop assigns v, y, l;
*/
while (1) {
      if (y>=n) {
          break;
      }
      v = v+3;
      y = y+1;
      v = v+2;
      l = l+3;
      l = v-l;
      v = v+1;
  }

}
