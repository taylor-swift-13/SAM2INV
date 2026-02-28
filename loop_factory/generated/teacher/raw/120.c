int main1(int k){
  int u, q, j;

  u=(k%6)+4;
  q=u;
  j=q;

  while (q-2>=0) {
      j = j+1;
      if (q+6<=q+u) {
          j = j+1;
      }
      q = q-2;
  }

}
