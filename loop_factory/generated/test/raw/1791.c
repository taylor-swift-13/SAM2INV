int main1(){
  int cb, hu, v, lt, kc, fwt;

  cb=1+7;
  hu=1;
  v=hu;
  lt=1;
  kc=hu;
  fwt=(1%6)+2;

  while (1) {
      if (kc>=cb) {
          break;
      }
      v = v*fwt+1;
      lt = lt*fwt;
      kc += 1;
  }

}
