int main1(int a,int p){
  int u, v, j;

  u=p;
  v=0;
  j=4;

  while (1) {
      j = j+3;
      if ((v%6)==0) {
          j = j+v;
      }
      j = j+j;
  }

}
