int main1(int o){
  int ab0l, c, rqx;

  ab0l=0;
  c=(o%20)+10;
  rqx=(o%15)+8;

  for (; c>0&&rqx>0; ab0l = ab0l + 1) {
      if (!(!(ab0l%2==0))) {
          c--;
      }
      else {
          rqx = rqx - 1;
      }
  }

}
