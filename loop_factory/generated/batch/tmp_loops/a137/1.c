int main1(int m,int p){
  int h, s, c, v;

  h=59;
  s=0;
  c=3;
  v=-6;

  while (s+1<=h) {
      if (c+5<=h) {
          c = c+5;
      }
      else {
          c = h;
      }
      c = c+v+v;
      c = c+1;
  }

}
