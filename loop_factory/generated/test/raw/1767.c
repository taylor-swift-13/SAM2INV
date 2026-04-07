int main1(){
  int qp5, jw, ll, gmf;

  qp5=1+9;
  jw=0;
  ll=0;
  gmf=jw;

  while (jw < qp5) {
      jw = jw + 1;
      ll = ll + jw * jw;
      gmf = gmf*4+(ll%4)+0;
  }

}
