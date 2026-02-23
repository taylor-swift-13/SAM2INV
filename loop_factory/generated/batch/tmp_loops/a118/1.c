int main1(int a,int m){
  int l, v, y;

  l=a;
  v=0;
  y=v;

  while (v<l) {
      if ((v%6)==0) {
          y = y+1;
      }
      else {
          y = y+v;
      }
      v = v+2;
  }

}
