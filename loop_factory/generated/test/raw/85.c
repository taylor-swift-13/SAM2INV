int main1(){
  int zn, v5j, ocj;

  zn=(1%38)+4;
  v5j=0;
  ocj=v5j;

  while (1) {
      if (ocj+3<=zn) {
          ocj = ocj + 3;
      }
      else {
          ocj = zn;
      }
      ocj++;
      v5j++;
      if (v5j>=zn) {
          break;
      }
  }

}
