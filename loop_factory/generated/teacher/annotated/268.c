int main1(int k,int m){
  int l, r, i;

  l=10;
  r=l;
  i=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 10;
  loop invariant 0 <= r;
  loop invariant r <= l;
  loop invariant i % 5 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant i <= -5;
  loop invariant r >= 0;
  loop invariant (r >= 9) ==> i == -5;
  loop assigns i, r;
*/
while (r>=1) {
      if ((r%9)==0) {
          i = i+i;
      }
      r = r-1;
  }

}
