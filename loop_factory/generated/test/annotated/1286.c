int main1(int t){
  int mhs, kw, h, ska8, oh, nrv;
  mhs=21;
  kw=0;
  h=t;
  ska8=mhs;
  oh=kw;
  nrv=kw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nrv == t * kw;
  loop invariant oh  == kw * (kw - 1) / 2;
  loop invariant ska8 == mhs - kw;
  loop invariant h   == t + kw;
  loop invariant mhs >= kw;
  loop assigns nrv, oh, ska8, h, kw;
*/
while (1) {
      nrv += t;
      oh += kw;
      ska8--;
      h += 1;
      kw++;
      if (kw>=mhs) {
          break;
      }
  }
}