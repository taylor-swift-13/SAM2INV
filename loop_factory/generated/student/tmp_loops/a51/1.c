int main1(int b,int m){
  int y, g, v;

  y=(m%31)+9;
  g=y;
  v=g;

  while (g>=2) {
      v = v+4;
      if (g+3<=m+y) {
          v = v+1;
      }
      v = v+2;
      v = v+g;
  }

}
