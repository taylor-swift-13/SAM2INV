int main1(int t,int r){
  int fjw4, eld, awq, x8, oi;

  fjw4=t;
  eld=0;
  awq=0;
  x8=t;
  oi=t*2;

  while (awq<=fjw4-1) {
      x8 = awq;
      awq = awq + 5;
      oi = oi + awq;
  }

  while (fjw4<eld) {
      fjw4++;
      x8 += t;
      r += x8;
  }

}
