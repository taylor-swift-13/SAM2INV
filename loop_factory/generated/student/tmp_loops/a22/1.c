int main1(int b,int p){
  int m, c, v;

  m=b+20;
  c=m;
  v=p;

  while (c>=1) {
      v = v+3;
      v = v+c;
      if (v+6<m) {
          v = v+v;
      }
  }

}
