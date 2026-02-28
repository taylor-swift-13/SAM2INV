int main1(int a,int m){
  int h, s, p, w;

  h=(m%25)+17;
  s=0;
  p=6;
  w=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == (\at(m, Pre) % 25) + 17;
  loop invariant p >= 6;
  loop invariant a == \at(a, Pre);
  loop invariant w <= p - 2;
  loop invariant m == \at(m, Pre);
  loop invariant w <= p - 1;
  loop invariant (p == 6 && w == -1) || (w == p - 2);
  loop invariant h == ((\at(m, Pre) % 25) + 17);
  loop assigns w, p;
*/
while (1) {
      w = p;
      p = p+1;
      w = w-1;
  }

}
