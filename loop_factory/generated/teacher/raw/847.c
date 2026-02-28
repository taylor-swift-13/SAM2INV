int main1(int m,int p,int q){
  int b, y, o, v;

  b=q;
  y=2;
  o=b;
  v=b;

  while (1) {
      if (y>=b) {
          break;
      }
      o = o+1;
      y = y+1;
      o = o+5;
      v = v+3;
      if (v+7<b) {
          v = o-v;
      }
      else {
          o = o+v;
      }
      o = o+1;
  }

}
