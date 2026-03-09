int main1(int z,int o){
  int ji, yymw, vxmq, iie;

  ji=(z%19)+14;
  yymw=0;
  vxmq=0;
  iie=20;

  while (1) {
      if (!(yymw<=ji-1)) {
          break;
      }
      yymw += 1;
      if (yymw<=iie) {
          iie = yymw;
      }
      vxmq = vxmq + ji;
  }

}
