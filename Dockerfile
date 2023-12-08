FROM minizinc/minizinc:latest

WORKDIR ./CDMO_Proj_Pivi_Fusconi_Oshodi_Marzi

COPY . .

RUN apt-get update
RUN apt-get install -y python3.10
RUN apt-get install -y python3-pip
RUN apt-get install -y glpk-utils
RUN python3 -m pip install -r requirements.txt
RUN apt-get install -y z3
RUN apt-get install -y cvc4
RUN apt-get install -y dos2unix
RUN dos2unix SMT/src/binary.sh \
    && chmod +x SMT/src/binary.sh \
    && dos2unix SMT/src/linear.sh \
   && chmod +x SMT/src/linear.sh \
   && apt-get install -y bash coreutils



CMD  python3 main.py -a cp -n 0  && python3 main.py -a sat -n 6 && python3 main.py -a smt -n 7 && python3 main.py -a smtlib -n 1 && python3 main.py -a lp -n 4
