int main1(int n,int q){
  int h, d, w;

  h=26;
  d=h;
  w=d;

  while (d>0) {
      w = w*2;
      if (w+5<h) {
          w = w*w+w;
      }
      else {
          w = w*2;
      }
      d = d-1;
  }

}
