int main1(int n,int e){
  int jv, qxsh, em, you, dtw;

  jv=n-4;
  qxsh=0;
  em=0;
  you=3;
  dtw=jv;

  while (1) {
      if (!(qxsh<jv&&you>0)) {
          break;
      }
      qxsh += 1;
      em = em + you;
      you -= 1;
      dtw += jv;
  }

}
