int main1(int k,int p){
  int u, i, v;

  u=63;
  i=u;
  v=p;

  while (i>0) {
      v = v+2;
      v = v*v;
      if ((i%6)==0) {
          v = v*v+v;
      }
  }

}
