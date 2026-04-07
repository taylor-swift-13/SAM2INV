int main1(){
  int o4r, eco, bkh, qsp3, kd7, os;

  o4r=1;
  eco=1;
  bkh=4;
  qsp3=eco;
  kd7=o4r;
  os=(1%35)+8;

  while (os>0) {
      kd7 = kd7+os*os;
      bkh = bkh+qsp3*qsp3;
      qsp3 = qsp3+os*os;
      os -= 1;
      bkh = bkh*4;
  }

}
