int main1(int b,int k){
  int p, q, v, r;

  p=(k%7)+8;
  q=0;
  v=p;
  r=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == p;
  loop invariant p == (k % 7) + 8;
  loop invariant p == (\at(k, Pre) % 7) + 8;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == ((\at(k, Pre) % 7) + 8);

  loop assigns v;
*/
while (1) {
      if (v+6<=p) {
          v = v+6;
      }
      else {
          v = p;
      }
  }

}
