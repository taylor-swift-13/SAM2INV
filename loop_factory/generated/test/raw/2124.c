int main1(){
  int uyo1, fhpy, hl, k5ye, jn;

  uyo1=8;
  fhpy=uyo1;
  hl=uyo1 - 1;
  k5ye=uyo1;
  jn=uyo1 - 2;

  while (fhpy > 0) {
      k5ye -= 1;
      fhpy -= 1;
      jn = (hl = k5ye - 1, k5ye - 2);
      hl += jn;
  }

}
