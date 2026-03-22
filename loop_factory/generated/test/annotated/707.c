int main1(int i,int f){
  int rf, nn62, mik, v, ru, fp;
  rf=0;
  nn62=i;
  mik=0;
  v=rf;
  ru=(i%35)+8;
  fp=rf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == mik;
  loop invariant ru <= ((\at(i,Pre) % 35) + 8);
  loop invariant 0 <= v;
  loop invariant v == ((((i % 35) + 8) * (((i % 35) + 8) + 1) * (2 * ((i % 35) + 8) + 1)) / 6) - (((ru) * ((ru) + 1) * (2 * (ru) + 1)) / 6);
  loop invariant rf == 0;
  loop assigns v, nn62, mik, fp, ru;
*/
while (ru>0) {
      v = v+ru*ru;
      nn62 = nn62+mik*mik;
      mik = mik+ru*ru;
      fp = fp+v+nn62;
      ru--;
  }
}