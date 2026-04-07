int main1(int y){
  int lq, zd, jg, c;

  lq=y*3;
  zd=lq;
  jg=0;
  c=1;

  while (c<=lq) {
      if (!(!(zd%2==0))) {
          jg += 1;
      }
      else {
          jg = jg - 1;
      }
      c = c + 1;
  }

}
