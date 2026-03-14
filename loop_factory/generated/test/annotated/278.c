int main1(int k,int h){
  int ah, p, a0, w8xs, itj, xfd;
  ah=(h%7)+11;
  p=0;
  a0=0;
  w8xs=0;
  itj=0;
  xfd=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ah == ((\at(h, Pre) % 7) + 11);
  loop invariant 0 <= w8xs <= 4;
  loop invariant 0 <= itj <= 4;
  loop invariant xfd == 7 + (p + 1) / 2;
  loop invariant -4 * p <= a0 <= 4 * p;
  loop invariant (p == 0) ==> (w8xs == 0);
  loop invariant 0 <= p;
  loop invariant p <= ah;
  loop invariant ah == (h % 7) + 11;
  loop assigns a0, p, w8xs, itj, xfd;
*/
while (p<ah) {
      w8xs = p%5;
      if (!(!(p>=xfd))) {
          itj = (p-xfd)%5;
          a0 = a0+w8xs-itj;
      }
      else {
          a0 += w8xs;
      }
      p++;
      xfd = xfd+(p%2);
  }
}