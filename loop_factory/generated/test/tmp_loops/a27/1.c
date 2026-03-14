int main1(){
  int e, c, lg, j, uj;

  e=36;
  c=0;
  lg=1;
  j=0;
  uj=e;

  while (c<e) {
      j = j+lg*c;
      uj = uj + c;
      c = e;
  }

  while (lg<e) {
      uj++;
      lg++;
      j = j + e;
  }

}
