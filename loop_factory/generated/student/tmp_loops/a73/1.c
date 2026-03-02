int main1(int b,int p){
  int r, t, v;

  r=20;
  t=1;
  v=t;

  while (1) {
      v = v+4;
      if ((t%6)==0) {
          v = v*v;
      }
      else {
          v = v*v+v;
      }
  }

}
