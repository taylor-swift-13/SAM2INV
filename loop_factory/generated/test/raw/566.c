int main1(int c){
  int si, hl36, jd, wv, w;

  si=c;
  hl36=0;
  jd=hl36;
  wv=c;
  w=5;

  while (hl36<si) {
      wv -= 4;
      jd += 4;
      w = w + wv;
      hl36 = si;
  }

}
