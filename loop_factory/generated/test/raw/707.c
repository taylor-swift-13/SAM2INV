int main1(int i,int f){
  int rf, nn62, mik, v, ru, fp;

  rf=0;
  nn62=i;
  mik=0;
  v=rf;
  ru=(i%35)+8;
  fp=rf;

  while (ru>0) {
      v = v+ru*ru;
      nn62 = nn62+mik*mik;
      mik = mik+ru*ru;
      fp = fp+v+nn62;
      ru--;
  }

}
