int main1(int b,int k){
  int p, q, v, r;

  p=(k%7)+8;
  q=0;
  v=p;
  r=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant r == 0;
  loop invariant p == (k % 7) + 8;
  loop invariant v >= p;

  loop invariant p == (\at(k, Pre) % 7) + 8;
  loop invariant p == ((\at(k, Pre) % 7) + 8);
  loop assigns v, r;
*/
while (1) {
      v = v*4;
      r = r/4;
  }

}
