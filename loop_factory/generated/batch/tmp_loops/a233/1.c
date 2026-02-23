int main1(int b,int p){
  int q, i, v;

  q=(p%32)+5;
  i=q;
  v=i;

  while (i>2) {
      if ((i%8)==0) {
          v = v*v+v;
      }
      else {
          v = v%6;
      }
      i = i-3;
  }

}
