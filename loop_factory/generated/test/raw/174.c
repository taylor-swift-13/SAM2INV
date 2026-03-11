int main1(int f){
  int du, djh2, j, c2, u, b;

  du=190;
  djh2=0;
  j=40;
  c2=0;
  u=1;
  b=0;

  while (j>0&&djh2<du) {
      if (j<=u) {
          b = j;
      }
      else {
          b = u;
      }
      c2 += b;
      djh2 = djh2 + 1;
      u = u + 1;
      j -= b;
  }

}
