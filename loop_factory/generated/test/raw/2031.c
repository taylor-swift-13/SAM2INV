int main1(){
  int nh, vf, v6, g, mz;

  nh=1;
  vf=0;
  v6=-6;
  g=nh;
  mz=nh;

  while (vf < nh) {
      mz = mz+(v6%5);
      vf++;
      v6 = v6*2;
      g += v6;
  }

}
