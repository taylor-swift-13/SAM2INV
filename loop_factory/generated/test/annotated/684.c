int main1(){
  int h7d, ln, ipp, ytz, r71;
  h7d=1+7;
  ln=1;
  ipp=(1%40)+2;
  ytz=0;
  r71=ln;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((r71 - 1) % h7d == 0);
  loop invariant ipp != ytz;
  loop invariant ipp >= 1;
  loop invariant (0 <= ytz && ytz <= 3);
  loop invariant (r71 >= 1);
  loop invariant (ipp == 2) || (ipp == 3);
  loop assigns ytz, r71, ipp;
*/
while (ipp!=ytz) {
      ytz = ipp;
      r71 = r71 + h7d;
      ipp = (ipp+h7d/ipp)/2;
  }
}