int main1(int e){
  int pjx, t2r, vjwm;
  pjx=0;
  t2r=(e%28)+10;
  vjwm=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t2r == ((\at(e, Pre) % 28) + 10) - (pjx * (pjx - 1)) / 2;
  loop invariant 0 <= pjx;
  loop invariant t2r == (((e % 28) + 10) - ((pjx * (pjx - 1)) / 2));
  loop assigns t2r, pjx, vjwm;
*/
while (t2r>pjx) {
      t2r -= pjx;
      pjx += 1;
      vjwm = vjwm+(t2r%6);
  }
}