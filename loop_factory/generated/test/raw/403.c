int main1(int p,int b){
  int grw, vb, d, v, hw;

  grw=p-8;
  vb=grw;
  d=20;
  v=1;
  hw=0;

  while (d>0&&v<=grw) {
      if (!(d<=v)) {
          d = 0;
      }
      else {
          d -= v;
      }
      vb = vb + 1;
      v++;
      hw++;
  }

}
