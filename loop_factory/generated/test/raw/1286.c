int main1(int t){
  int mhs, kw, h, ska8, oh, nrv;

  mhs=21;
  kw=0;
  h=t;
  ska8=mhs;
  oh=kw;
  nrv=kw;

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
