int main1(int b,int k){
  int h, s, p, v;

  h=k;
  s=2;
  p=-8;
  v=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == k;
  loop invariant s >= 2;
  loop invariant p == 3*s - 14;
  loop invariant 2*v == 2*h + 3*s*s - 25*s + 38;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 2*v == 2*h - 16*(s - 2) + 3*(s - 2)*(s - 1);
  loop invariant v == h - 8*(s-2) + (3*(s-2)*(s-1))/2;
  loop invariant v == k - 8*(s-2) + 3*(s-2)*(s-1)/2;
  loop assigns p, s, v;
*/
while (1) {
      if (s>=h) {
          break;
      }
      p = p+2;
      s = s+1;
      p = p+1;
      v = v+p;
  }

}
