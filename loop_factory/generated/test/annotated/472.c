int main1(int y){
  int hr, s5, p7f, di, c2;
  hr=(y%31)+17;
  s5=0;
  p7f=(y%18)+5;
  di=(y%15)+3;
  c2=p7f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (di - p7f) == ((\at(y,Pre) % 15) + 3) - ((\at(y,Pre) % 18) + 5);
  loop invariant c2 == ((\at(y,Pre) % 18) + 5);
  loop invariant p7f <= ((\at(y,Pre) % 18) + 5);
  loop assigns di, p7f, c2;
*/
while (1) {
      if (!(p7f!=0)) {
          break;
      }
      di -= 1;
      p7f = p7f - 1;
      c2 += s5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant di - (2*y + 1) * p7f == (\at(y,Pre) % 15 + 3) - ((\at(y,Pre) % 18) + 5);
  loop invariant p7f >= 0;
  loop assigns di, p7f;
*/
while (1) {
      if (!(p7f+1<=hr)) {
          break;
      }
      di = di+y+y;
      di++;
      p7f += 1;
  }
}