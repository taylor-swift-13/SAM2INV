int main1(){
  int qmdk, qp4w, rj, v1, j9, bs1;

  qmdk=64;
  qp4w=3;
  rj=14;
  v1=0;
  j9=1;
  bs1=0;

  while (rj>0&&qp4w<qmdk) {
      if (rj<=j9) {
          bs1 = rj;
      }
      else {
          bs1 = j9;
      }
      v1 += bs1;
      qp4w = qp4w + 1;
      j9++;
      rj -= bs1;
  }

}
