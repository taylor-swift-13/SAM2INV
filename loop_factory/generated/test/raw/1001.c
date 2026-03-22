int main1(){
  int nc, czn, mreu, jeo, w2;

  nc=1-5;
  czn=nc;
  mreu=20;
  jeo=1;
  w2=0;

  while (mreu>0&&jeo<=nc) {
      if (!(mreu<=jeo)) {
          mreu = 0;
      }
      else {
          mreu -= jeo;
      }
      w2++;
      czn++;
      jeo = jeo + 1;
  }

}
