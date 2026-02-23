int main1(int a,int b){
  int v, t, y;

  v=62;
  t=0;
  y=b;

  while (t<v) {
      y = y+t;
      if (t+4<=a+v) {
          y = y+1;
      }
      t = t+4;
  }

}
