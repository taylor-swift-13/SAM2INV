int main1(int a,int p){
  int r, j, y, v;

  r=(a%24)+13;
  j=2;
  y=p;
  v=p;

  while (1) {
      if (j>=r) {
          break;
      }
      y = y+2;
      j = j+1;
  }

}
