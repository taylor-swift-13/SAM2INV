int main1(int y){
  int s4, xt, v0, xu, aly;

  s4=y+18;
  xt=s4;
  v0=0;
  xu=0;
  aly=4;

  while (v0<s4&&aly>0) {
      xu += aly;
      v0++;
      y += xt;
      aly = aly - 1;
  }

}
