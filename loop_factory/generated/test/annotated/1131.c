int main1(int c,int a){
  int f, kj, s, pds, agkc, j7yb, nl;
  f=54;
  kj=-6;
  s=0;
  pds=0;
  agkc=0;
  j7yb=5;
  nl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= s);
  loop invariant (s <= j7yb);
  loop invariant (nl == kj + 6);
  loop invariant s == pds - agkc;
  loop invariant kj <= f;
  loop invariant agkc >= 0;
  loop invariant pds >= 0;
  loop invariant 0 <= nl;
  loop invariant s <= 5;
  loop invariant agkc <= nl;
  loop invariant agkc + pds <= nl;
  loop assigns s, agkc, pds, kj, nl;
*/
while (kj<f) {
      if (kj%3==0) {
          if (s>0) {
              s -= 1;
              agkc++;
          }
      }
      else {
          if (s<j7yb) {
              s++;
              pds = pds + 1;
          }
      }
      kj = kj + 1;
      nl += 1;
  }
}