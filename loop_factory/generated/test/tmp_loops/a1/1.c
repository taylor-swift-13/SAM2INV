int main1(){
  int tn, baml, i, qoa;

  tn=45;
  baml=0;
  i=0;
  qoa=1;

  for (; baml<tn; baml++) {
      if (i>=4) {
          qoa = -1;
      }
      if (!(i>0)) {
          qoa = 1;
      }
      i = i + qoa;
  }

}
