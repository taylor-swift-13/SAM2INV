int main1(int k,int m){
  int g, l, v;

  g=m;
  l=0;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == m;
  loop invariant l == 0;
  loop invariant v >= 1;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant g == \at(m, Pre);
  loop assigns v;
*/
while (1) {
      v = v+3;
      if (l+1<=v+g) {
          v = v+1;
      }
  }

}
